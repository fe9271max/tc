import re
import zipfile
import geoip2.database
import os
import sys
import platform
import subprocess
import tempfile
import time
import json
import argparse
import logging
import threading
import queue
import requests
import shutil
import base64
import binascii
from urllib.parse import urlparse, parse_qs, unquote
from base64 import urlsafe_b64decode, urlsafe_b64encode
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime
from pathlib import Path
from bs4 import BeautifulSoup
from collections import defaultdict

sys.stdout.reconfigure(encoding='utf-8')  # type: ignore

# Organized directory structure for data storage
BASE_DIR = Path(os.path.dirname(os.path.abspath(__file__)))
PROTOCOLS_DIR = BASE_DIR / "Servers" / "Protocols"
REGIONS_DIR = BASE_DIR / "Servers" / "Regions"
REPORTS_DIR = BASE_DIR / "logs"
MERGED_DIR = BASE_DIR / "Servers" / "Merged"
CHANNELS_DIR = BASE_DIR / "Servers" / "Channels"
CHANNELS_FILE = BASE_DIR / "data" / "telegram_sources.txt"
LOG_FILE = REPORTS_DIR / "extraction_report.log"
GEOIP_DATABASE_PATH = BASE_DIR / "data" / "db" / "GeoLite2-Country.mmdb"
MERGED_SERVERS_FILE = MERGED_DIR / "merged_servers.txt"
SLEEP_TIME = 3
BATCH_SIZE = 10
FETCH_CONFIG_LINKS_TIMEOUT = 15
MAX_CHANNEL_SERVERS = 20
MAX_PROTOCOL_SERVERS = 10000
MAX_REGION_SERVERS = 10000
MAX_MERGED_SERVERS = 100000
V2RAY_BIN = 'v2ray' if platform.system() == 'Linux' else 'v2ray.exe'
V2RAY_DIR = BASE_DIR / 'data' / 'v2ray'
TESTED_SERVERS_DIR = BASE_DIR / 'Tested_Servers'
LOGS_DIR = BASE_DIR / 'logs'
TEST_LINK = "http://httpbin.org/get"
MAX_THREADS = 20
START_PORT = 10000
REQUEST_TIMEOUT = 30
PROCESS_START_WAIT = 15
REALTIME_UPDATE_INTERVAL = 25
ENABLED_PROTOCOLS = {
    'vless': True,
    'vmess': False,
    'trojan': False,
    'ss': False,
    'hysteria': False,
    'hysteria2': False,
    'tuic': False,
    'wireguard': False,
    'warp': False,
}
channel_test_stats = defaultdict(
    lambda: {'total_prepared': 0, 'active': 0, 'failed': 0, 'skip': 0})

# Use a frozenset for immutable patterns keys
PATTERNS = {
    'vmess': r'(?<![a-zA-Z0-9_])vmess://[^\s<>]+',
    'vless': r'(?<![a-zA-Z0-9_])vless://[^\s<>]+',
    'trojan': r'(?<![a-zA-Z0-9_])trojan://[^\s<>]+',
    'hysteria': r'(?<![a-zA-Z0-9_])hysteria://[^\s<>]+',
    'hysteria2': r'(?<![a-zA-Z0-9_])hysteria2://[^\s<>]+',
    'tuic': r'(?<![a-zA-Z0-9_])tuic://[^\s<>]+',
    'ss': r'(?<![a-zA-Z0-9_])ss://[^\s<>]+',
    'wireguard': r'(?<![a-zA-Z0-9_])wireguard://[^\s<>]+',
    'warp': r'(?<![a-zA-Z0-9_])warp://[^\s<>]+'
}


def clean_directory(dir_path: Path):
    """Clean a directory, with special handling for the V2Ray directory."""
    dir_path = dir_path.resolve()
    is_v2ray_dir = dir_path == V2RAY_DIR.resolve()

    if dir_path.exists():
        if is_v2ray_dir:
            logging.info(f"Selectively cleaning V2Ray directory: {dir_path}")
            for item in dir_path.iterdir():
                if item.name == V2RAY_BIN or item.suffix.lower() in ['.dat', '.db'] or item.name.lower() in ['geoip.dat', 'geosite.dat']:
                    logging.debug(f"Skipping deletion of essential V2Ray file: {item}")
                    continue
                try:
                    if item.is_file() or item.is_symlink():
                        item.unlink()
                    elif item.is_dir():
                        shutil.rmtree(item)
                except Exception as e:
                    logging.error(f"Failed to delete {item} during V2Ray dir selective clean: {str(e)}")
            dir_path.mkdir(exist_ok=True)
            return

        for item in dir_path.iterdir():
            try:
                if item.is_file() or item.is_symlink():
                    item.unlink()
                elif item.is_dir():
                    shutil.rmtree(item)
            except Exception as e:
                logging.error(f"Failed to delete {item}: {str(e)}")
        logging.info(f"Cleaned directory: {dir_path}")
    else:
        dir_path.mkdir(parents=True, exist_ok=True)
        logging.info(f"Created directory: {dir_path}")


logging.info("Cleaning extraction directories (Servers folder)...")
servers_dir = BASE_DIR / "Servers"
if servers_dir.exists():
    shutil.rmtree(servers_dir)
    logging.info(f"Removed existing directory: {servers_dir}")

# Create all required directories
for directory in [
    PROTOCOLS_DIR, REGIONS_DIR, REPORTS_DIR, MERGED_DIR, CHANNELS_DIR,
    V2RAY_DIR, TESTED_SERVERS_DIR, LOGS_DIR,
    TESTED_SERVERS_DIR / 'Protocols',
    TESTED_SERVERS_DIR / 'Channels'
]:
    directory.mkdir(parents=True, exist_ok=True)


def normalize_telegram_url(url: str) -> str:
    """Normalize various Telegram URL formats to https://t.me/s/ format.
    Args:
        url: Input URL string to normalize
    Returns:
        Normalized URL in https://t.me/s/ format or empty string for invalid URLs
    """
    if not url:
        return ""
    url = url.strip()
    # Handle bare username cases (e.g., "Free_HTTPCustom")
    if not any(url.startswith(prefix) for prefix in ["http://", "https://", "t.me/", "@"]):
        if "/" not in url:  # Confirm it's just a channel name without paths
            return f"https://t.me/s/{url}"
    # Convert t.me/ links to https://t.me/s/
    if url.startswith("t.me/"):
        url = f"https://{url}"
    # Convert @username format to https://t.me/s/username
    if url.startswith("@"):
        return f"https://t.me/s/{url[1:]}"
    # Process full https://t.me/ URLs
    if url.startswith("https://t.me/"):
        parts = url.split('/')
        if len(parts) >= 4:
            channel_candidate = parts[3]
            if channel_candidate == 's':
                if len(parts) > 4 and parts[4]:  # Valid /s/ link
                    return url
                return ""  # Invalid /s/ link like https://t.me/s/
            else:  # Convert to /s/ format
                # Handle cases like https://t.me/channelname/123 by taking only channelname
                return f"https://t.me/s/{parts[3]}"
        return ""  # Invalid URL structure
    return url  # Return as-is if already in /s/ format or other valid format


def extract_channel_name(url: str) -> str:
    try:
        parsed_url = urlparse(url)
        path_parts = [part for part in parsed_url.path.split('/') if part]
        if path_parts:
            if path_parts[0] == 's' and len(path_parts) > 1:
                return path_parts[1]
            return path_parts[0]
    except Exception:
        pass
    # Fallback for simple names or if parsing fails badly
    name_candidate = url.split('/')[-1] if '/' in url else url
    # Remove query parameters or fragments from the name if they got included
    name_candidate = name_candidate.split('?')[0].split('#')[0]
    return name_candidate if name_candidate else "unknown_channel"


def count_servers_in_file(file_path: Path) -> int:
    if not file_path.exists():
        return 0
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            return len([line for line in f if line.strip() and not line.strip().startswith('#')])
    except Exception as e:
        logging.error(f"❌ Error counting servers in {file_path}: {e}")
        return 0


def get_current_counts():
    counts = {}
    for proto in PATTERNS:
        counts[proto] = count_servers_in_file(PROTOCOLS_DIR / f"{proto}.txt")
    counts['total'] = count_servers_in_file(MERGED_SERVERS_FILE)
    regional_servers = 0
    country_data = {}
    if REGIONS_DIR.exists():
        for region_file in REGIONS_DIR.glob("*.txt"):
            country = region_file.stem
            count = count_servers_in_file(region_file)
            country_data[country] = count
            regional_servers += count
    counts['successful'] = regional_servers
    counts['failed'] = max(0, counts['total'] - regional_servers)
    return counts, country_data


def get_channel_stats():
    channel_stats = {}
    if CHANNELS_DIR.exists():
        for channel_file in CHANNELS_DIR.glob("*.txt"):
            channel_stats[channel_file.stem] = count_servers_in_file(channel_file)
    return channel_stats


def save_extraction_data(channel_stats_data, country_data_map):
    current_counts, country_stats_map_local = get_current_counts()
    try:
        REPORTS_DIR.mkdir(exist_ok=True)
        with open(LOG_FILE, 'w', encoding='utf-8') as log:
            log.write("=== Country Statistics ===\n")
            log.write(f"Total Servers (Merged): {current_counts['total']}\n")
            log.write(f"Successful Geo-IP Resolutions: {current_counts['successful']}\n")
            log.write(f"Failed Geo-IP Resolutions: {current_counts['failed']}\n")
            for country, count in sorted(country_stats_map_local.items(), key=lambda x: x[1], reverse=True):
                log.write(f"{country:<20} : {count}\n")
            log.write("\n=== Server Type Summary ===\n")
            valid_protocols = {p: current_counts.get(p, 0) for p in PATTERNS}
            for proto, count in sorted(valid_protocols.items(), key=lambda x: x[1], reverse=True):
                log.write(f"{proto.upper():<20} : {count}\n")
            log.write("\n=== Channel Statistics (Extraction) ===\n")
            if not channel_stats_data:
                log.write("No channel data available.\n")
            else:
                for channel, total in sorted(channel_stats_data.items(), key=lambda x: x[1], reverse=True):
                    log.write(f"{channel:<30}: {total}\n")
    except Exception as e:
        logging.error(f"❌ Error writing extraction report to {LOG_FILE}: {e}")


def fetch_config_links(url: str):
    logging.info(f"Fetching configs from: {url}")
    try:
        headers = {'User-Agent': 'Mozilla/5.0'}
        response = requests.get(url, timeout=FETCH_CONFIG_LINKS_TIMEOUT, headers=headers)
        response.raise_for_status()
        soup = BeautifulSoup(response.content, 'html.parser')
        message_containers = soup.select('div.tgme_widget_message_bubble, div.tgme_widget_message_text')
        code_blocks = soup.find_all(['code', 'pre'])
        configs = {proto: set() for proto in PATTERNS}
        configs["all"] = set()

        for code_tag in code_blocks:
            clean_text = re.sub(r'(^`{1,3}|`{1,3}$)', '', code_tag.get_text('\n').strip(), flags=re.MULTILINE).strip()
            for line in clean_text.splitlines():
                line = line.strip()
                if not line:
                    continue
                for proto, pattern in PATTERNS.items():
                    valid_matches = set()
                    matches = re.findall(pattern, line)
                    if matches:
                        valid_matches = {m for m in matches if urlparse(m).scheme == proto}
                    if valid_matches:
                        configs[proto].update(valid_matches)
                        configs["all"].update(valid_matches)

        for container in message_containers:
            for line in container.get_text(separator='\n', strip=True).splitlines():
                line = line.strip()
                if not line:
                    continue
                for proto, pattern in PATTERNS.items():
                    valid_matches = set()
                    matches = re.findall(pattern, line)
                    if matches:
                        valid_matches = {m for m in matches if urlparse(m).scheme == proto}
                    if valid_matches:
                        configs[proto].update(valid_matches)
                        configs["all"].update(valid_matches)

        final_configs = {k: list(v) for k, v in configs.items() if v}
        logging.info(f"Found {len(final_configs.get('all', []))} potential configs in {url}")
        return final_configs
    except requests.exceptions.Timeout:
        logging.error(f"Timeout fetching {url}")
        return None
    except requests.exceptions.RequestException as e:
        logging.error(f"Connection error for {url}: {e}")
        return None
    except Exception as e:
        logging.error(f"Scraping error for {url}: {e}")
        return None


def load_existing_configs():
    existing = {proto: set() for proto in PATTERNS}
    existing["merged"] = set()
    for proto in PATTERNS:
        p_file = PROTOCOLS_DIR / f"{proto}.txt"
        if p_file.exists():
            try:
                with open(p_file, 'r', encoding='utf-8') as f:
                    existing[proto] = {l.strip() for l in f if l.strip()}
            except Exception as e:
                logging.error(f"Error reading {p_file}: {e}")
    if MERGED_SERVERS_FILE.exists():
        try:
            with open(MERGED_SERVERS_FILE, 'r', encoding='utf-8') as f:
                existing['merged'] = {l.strip() for l in f if l.strip()}
        except Exception as e:
            logging.error(f"Error reading {MERGED_SERVERS_FILE}: {e}")
    return existing


def trim_file(file_path: Path, max_lines: int):
    if not file_path.exists() or max_lines <= 0:
        return
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            lines = f.readlines()
        valid_lines = [line for line in lines if line.strip()]
        if len(valid_lines) > max_lines:
            logging.info(f"Trimming {file_path} from {len(valid_lines)} to {max_lines} lines.")
            with open(file_path, 'w', encoding='utf-8') as f:
                f.writelines(l if l.endswith('\n') else l + '\n' for l in valid_lines[:max_lines])
    except Exception as e:
        logging.error(f"Error trimming {file_path}: {e}")


def process_channel(url: str):
    channel_name = extract_channel_name(url)
    if not channel_name or channel_name == "unknown_channel":
        logging.warning(f"Could not extract a valid channel name from URL: {url}")
        return 0, 0
    channel_file = CHANNELS_DIR / f"{channel_name}.txt"
    logging.info(f"Processing channel: {channel_name} ({url})")
    existing_configs = load_existing_configs()
    configs = fetch_config_links(url)
    if configs is None or not configs.get("all"):
        logging.info(f"No new links or fetch failed for {channel_name}.")
        channel_file.touch(exist_ok=True)
        return 1 if configs is not None else 0, 0

    all_fetched = set(configs["all"])
    existing_channel_cfgs = set()
    if channel_file.exists():
        try:
            with open(channel_file, 'r', encoding='utf-8') as f:
                existing_channel_cfgs = {l.strip() for l in f if l.strip()}
        except Exception as e:
            logging.error(f"Error reading {channel_file}: {e}")

    new_for_channel = all_fetched - existing_channel_cfgs
    if new_for_channel:
        updated_ch_cfgs = list(new_for_channel) + list(existing_channel_cfgs)
        try:
            with open(channel_file, 'w', encoding='utf-8') as f:
                seen = set()
                unique_lines = [l for l in updated_ch_cfgs if not (l in seen or seen.add(l))]
                f.write('\n'.join(unique_lines[:MAX_CHANNEL_SERVERS]) + '\n')
            trim_file(channel_file, MAX_CHANNEL_SERVERS)
        except Exception as e:
            logging.error(f"Error writing {channel_file}: {e}")
    elif not channel_file.exists():
        channel_file.touch(exist_ok=True)

    new_global_total = 0
    for proto, links in configs.items():
        if proto == "all" or not links:
            continue
        new_global_proto = set(links) - existing_configs.get(proto, set())
        if not new_global_proto:
            continue
        proto_path = PROTOCOLS_DIR / f"{proto}.txt"
        try:
            updated_proto_lns = list(new_global_proto) + list(existing_configs.get(proto, set()))
            with open(proto_path, 'w', encoding='utf-8') as f:
                seen_proto = set()
                unique_proto_lines = [l for l in updated_proto_lns if not (l in seen_proto or seen_proto.add(l))]
                f.write('\n'.join(unique_proto_lines[:MAX_PROTOCOL_SERVERS]) + '\n')
            trim_file(proto_path, MAX_PROTOCOL_SERVERS)
            existing_configs[proto].update(new_global_proto)
        except Exception as e:
            logging.error(f"Error writing {proto_path}: {e}")

        new_for_merged = new_global_proto - existing_configs.get('merged', set())
        if new_for_merged:
            try:
                updated_merged_lns = list(new_for_merged) + list(existing_configs.get('merged', set()))
                with open(MERGED_SERVERS_FILE, 'w', encoding='utf-8') as f:
                    seen_merged = set()
                    unique_merged_lines = [l for l in updated_merged_lns if not (l in seen_merged or seen_merged.add(l))]
                    f.write('\n'.join(unique_merged_lines[:MAX_MERGED_SERVERS]) + '\n')
                trim_file(MERGED_SERVERS_FILE, MAX_MERGED_SERVERS)
                existing_configs['merged'].update(new_for_merged)
                new_global_total += len(new_for_merged)
            except Exception as e:
                logging.error(f"Error updating {MERGED_SERVERS_FILE}: {e}")

    logging.info(f"Channel {channel_name}: {len(new_for_channel)} new for channel file, {new_global_total} new globally.")
    return 1, new_global_total


def download_geoip_database():
    GEOIP_URL = "https://git.io/GeoLite2-Country.mmdb"
    GEOIP_DIR = GEOIP_DATABASE_PATH.parent
    logging.info(f"Attempting to download GeoIP database from {GEOIP_URL}...")
    try:
        GEOIP_DIR.mkdir(parents=True, exist_ok=True)
        with requests.get(GEOIP_URL, timeout=60, stream=True) as response:
            response.raise_for_status()
            with open(GEOIP_DATABASE_PATH, 'wb') as f:
                shutil.copyfileobj(response.raw, f)
        if GEOIP_DATABASE_PATH.stat().st_size > 1024 * 1024:
            logging.info("✅ GeoLite2 database downloaded successfully.")
            return True
        else:
            logging.error("❌ Downloaded GeoIP database seems too small. Deleting.")
            GEOIP_DATABASE_PATH.unlink(missing_ok=True)
            return False
    except requests.exceptions.RequestException as e:
        logging.error(f"❌ Failed to download GeoIP database: {e}")
        GEOIP_DATABASE_PATH.unlink(missing_ok=True)
        return False
    except Exception as e:
        logging.error(f"❌ An unexpected error occurred during GeoIP download: {e}")
        GEOIP_DATABASE_PATH.unlink(missing_ok=True)
        return False


def process_geo_data():
    if not GEOIP_DATABASE_PATH.exists() or GEOIP_DATABASE_PATH.stat().st_size < 1024 * 1024:
        if not download_geoip_database():
            logging.error("❌ Cannot perform GeoIP: Database download failed.")
            return {}
    geo_reader = None
    try:
        geo_reader = geoip2.database.Reader(str(GEOIP_DATABASE_PATH))
    except Exception as e:
        logging.error(f"❌ Error opening GeoIP DB: {e}")
        return {}

    country_configs = defaultdict(list)
    failed_lookups = 0
    processed = 0

    if REGIONS_DIR.exists():
        for rf in REGIONS_DIR.glob("*.txt"):
            try:
                rf.unlink()
            except OSError as e:
                logging.error(f"Error deleting old region file {rf}: {e}")
    else:
        REGIONS_DIR.mkdir(exist_ok=True)

    configs_for_geoip = []
    if MERGED_SERVERS_FILE.exists():
        try:
            with open(MERGED_SERVERS_FILE, 'r', encoding='utf-8') as f:
                configs_for_geoip = [l.strip() for l in f if l.strip()]
        except Exception as e:
            logging.error(f"Error reading merged servers for GeoIP: {e}")

    if not configs_for_geoip:
        logging.warning("No merged configs found to perform GeoIP analysis.")
        if geo_reader:
            geo_reader.close()
        return {}

    for config_link in configs_for_geoip:
        processed += 1
        ip_address = None
        country_code = "Unknown"
        try:
            parsed_link = urlparse(config_link)
            hostname = parsed_link.hostname
            if not hostname:
                failed_lookups += 1
                continue

            if parsed_link.scheme in ['vless', 'trojan', 'hysteria', 'hysteria2', 'tuic', 'ss']:
                ip_address = hostname
            elif parsed_link.scheme == 'vmess':
                try:
                    b64_payload = parsed_link.netloc + parsed_link.path
                    decoded_payload = urlsafe_b64decode(b64_payload + '=' * ((4 - len(b64_payload) % 4) % 4)).decode('utf-8')
                    vmess_data = json.loads(decoded_payload)
                    ip_address = vmess_data.get('add')
                except (binascii.Error, UnicodeDecodeError, json.JSONDecodeError) as e:
                    logging.debug(f"VMess decoding error for GeoIP on {config_link[:30]}...: {e}")
                    failed_lookups += 1
                    continue

            if ip_address:
                if not re.match(r"^\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}$", ip_address):
                    country_code = "Domain"
                else:
                    try:
                        response = geo_reader.country(ip_address)
                        country_code = response.country.iso_code or response.country.name or "Unknown"
                    except geoip2.errors.AddressNotFoundError: # type: ignore
                        country_code = "Unknown"
                        failed_lookups += 1
                    except Exception as geo_e:
                        logging.warning(f"GeoIP lookup error for IP {ip_address}: {geo_e}")
                        country_code = "Unknown"
                        failed_lookups += 1
            else:
                failed_lookups += 1
                country_code = "Unknown"
        except Exception as e:
            logging.warning(f"Error processing config for GeoIP '{config_link[:30]}...': {e}")
            failed_lookups += 1
            country_code = "Unknown"

        country_configs[country_code].append(config_link)

    if geo_reader:
        geo_reader.close()

    final_country_counts = {}
    for country_code, config_list in country_configs.items():
        final_country_counts[country_code] = len(config_list)
        try:
            safe_country_name = "".join(c if c.isalnum() else "_" for c in country_code)
            with open(REGIONS_DIR / f"{safe_country_name}.txt", 'w', encoding='utf-8') as f:
                f.write('\n'.join(config_list[:MAX_REGION_SERVERS]) + '\n')
        except Exception as e:
            logging.error(f"Error writing region file for {country_code}: {e}")

    logging.info(
        f"GeoIP analysis done. Total Processed: {processed}, Successful Lookups: {processed - failed_lookups}, Failed/Unknown: {failed_lookups}")
    return dict(final_country_counts)


class CleanFormatter(logging.Formatter):
    def format(self, record):
        if hasattr(record, 'clean_output'):
            if record.levelno == logging.INFO:
                return f"{record.msg}"
            elif record.levelno >= logging.WARNING:
                return f"{record.levelname}: {record.msg}"
        return super().format(record)


if not logging.getLogger().hasHandlers():
    logger = logging.getLogger()
    logger.setLevel(logging.INFO)
    ch = logging.StreamHandler(sys.stdout)
    cf = CleanFormatter()
    ch.addFilter(lambda r: setattr(r, 'clean_output', True) or True)
    ch.setFormatter(cf)
    logger.addHandler(ch)
    fh = logging.FileHandler(LOGS_DIR / 'testing_debug.log', encoding='utf-8')
    ff = logging.Formatter('%(asctime)s-%(levelname)s-%(threadName)s- %(message)s')
    fh.setFormatter(ff)
    logger.addHandler(fh)

try:
    import urllib3
    urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)
except ImportError:
    try:
        requests.packages.urllib3.disable_warnings(requests.packages.urllib3.exceptions.InsecureRequestWarning)  # type: ignore
    except AttributeError:
        pass

current_port = START_PORT
port_lock = threading.Lock()


def get_next_port():
    global current_port
    with port_lock:
        port = current_port
        current_port += 1
    return port


def read_links_from_file(file_path: Path):
    try:
        with open(file_path, "r", encoding="utf-8") as f:
            return [l.strip() for l in f if l.strip() and not l.strip().startswith('#')]
    except FileNotFoundError:
        logging.debug(f"File not found during read: {file_path}")
        return []
    except Exception as e:
        logging.error(f"Error reading links from {file_path}: {e}")
        return []


def parse_vless_link(link: str):
    parsed = urlparse(link)
    uuid = parsed.username
    query = parse_qs(parsed.query)
    hostname = parsed.hostname
    if not (parsed.scheme == 'vless' and hostname and uuid and
            re.match(r'^[0-9a-f]{8}-?[0-9a-f]{4}-?[0-9a-f]{4}-?[0-9a-f]{4}-?[0-9a-f]{12}$', uuid, re.I)):
        raise ValueError(f"Invalid VLESS link structure: {link}")
    port = parsed.port or (443 if query.get('security', [''])[0] in ['tls', 'reality'] else 80)
    sec = query.get('security', ['none'])[0] or 'none'
    net = query.get('type', ['tcp'])[0] or 'tcp'
    sni = query.get('sni', [hostname])[0] or hostname
    return {
        'original_link': link, 'protocol': 'vless', 'uuid': uuid.replace('-', ''), 'host': hostname, 'port': int(port),
        'security': sec, 'encryption': query.get('encryption', ['none'])[0] or 'none', 'network': net,
        'ws_path': query.get('path', ['/'])[0] if net == 'ws' else '/',
        'ws_host': query.get('host', [sni])[0] if net == 'ws' else sni,
        'sni': sni, 'pbk': query.get('pbk', [''])[0] if sec == 'reality' else '',
        'sid': query.get('sid', [''])[0] if sec == 'reality' else '',
        'fp': query.get('fp', [''])[0] if sec == 'reality' else '',
        'alpn': [v.strip() for v in query.get('alpn', [''])[0].split(',') if v.strip()],
        'flow': query.get('flow', [''])[0]
    }


def parse_vmess_link(link: str):
    parsed = urlparse(link)
    if parsed.scheme != 'vmess':
        raise ValueError(f"Invalid VMESS scheme: {link}")
    try:
        base64_part = parsed.netloc + parsed.path
        json_str = urlsafe_b64decode(base64_part + '=' * ((4 - len(base64_part) % 4) % 4)).decode('utf-8')
        data = json.loads(json_str)
    except Exception as e:
        raise ValueError(f"VMess JSON decode error for {link}: {e}")

    address = data.get('add', '')
    if not re.match(r"^[a-zA-Z0-9.-]+$", address):
        address = data.get('host', '')
        if not address:
            raise ValueError(f"VMess 'add' field is invalid and no fallback 'host' found: {data.get('add')}")

    port = int(data.get('port', 0))
    uuid = data.get('id')
    if not (address and port and uuid):
        raise ValueError(f"VMess missing address/port/id in {link}")

    clean_data = {
        "v": "2",
        "ps": f"vmess-{address}-{port}",
        "add": address,
        "port": str(port),
        "id": uuid,
        "aid": str(data.get("aid", 0)),
        "net": data.get("net", "tcp") or "tcp",
        "type": data.get("type", "none") or "none",
        "host": data.get("host", ""),
        "path": data.get("path", ""),
        "tls": data.get("tls", "") or "",
        "sni": data.get("sni", ""),
        "alpn": data.get("alpn", ""),
        "fp": data.get("fp", ""),
        "scy": data.get("scy", "auto") or "auto"
    }

    keys_to_remove = [k for k, v in clean_data.items() if v == "" and k not in ["ps", "add", "port", "id", "net", "tls"]]
    for k in keys_to_remove:
        del clean_data[k]

    clean_json_str = json.dumps(clean_data, separators=(',', ':'), sort_keys=True)
    rebuilt_b64 = urlsafe_b64encode(clean_json_str.encode('utf-8')).decode('utf-8').rstrip("=")
    rebuilt_link = f"vmess://{rebuilt_b64}"

    return {
        'original_link': rebuilt_link,
        'protocol': 'vmess',
        'uuid': uuid,
        'host': address,
        'port': port,
        'network': clean_data["net"],
        'security': clean_data["tls"],
        'ws_path': clean_data.get('path', '/') if clean_data["net"] == 'ws' else '/',
        'ws_host': clean_data.get('host', address) if clean_data["net"] == 'ws' else address,
        'sni': clean_data.get('sni', clean_data.get('host', address) if clean_data["tls"] == 'tls' else ''),
        'alter_id': int(clean_data["aid"]),
        'encryption': clean_data.get("scy", "auto")
    }


def parse_trojan_link(link: str):
    parsed = urlparse(link)
    passwd = parsed.username
    host = parsed.hostname
    port = parsed.port
    query = parse_qs(parsed.query)
    if not (parsed.scheme == 'trojan' and passwd and host and port):
        raise ValueError(f"Invalid Trojan link structure: {link}")
    sec = query.get('security', ['tls'])[0] or 'tls'
    sni = query.get('sni', [host])[0] or host
    net = query.get('type', ['tcp'])[0] or 'tcp'
    alpn_str = query.get('alpn', ['h2,http/1.1'])[0]
    alpn = [v.strip() for v in alpn_str.split(',') if v.strip()]
    return {
        'original_link': link, 'protocol': 'trojan', 'password': passwd, 'host': host, 'port': int(port),
        'security': sec, 'sni': sni, 'alpn': alpn, 'network': net,
        'ws_path': query.get('path', ['/'])[0] if net == 'ws' else '/',
        'ws_host': query.get('host', [sni])[0] if net == 'ws' else sni
    }


def parse_ss_link(link: str):
    parsed = urlparse(link)
    host = parsed.hostname
    port = parsed.port
    if not (parsed.scheme == 'ss' and host and port):
        raise ValueError(f"Invalid SS host/port in link: {link}")
    name = unquote(parsed.fragment) if parsed.fragment else f"ss_{host}"
    userinfo_raw = parsed.username
    method, password = None, None

    if userinfo_raw:
        try:
            decoded_userinfo = urlsafe_b64decode(userinfo_raw + '=' * ((4 - len(userinfo_raw) % 4) % 4)).decode('utf-8')
            if ':' in decoded_userinfo:
                method, password = decoded_userinfo.split(':', 1)
            else:
                raise ValueError("Decoded userinfo did not contain ':'")
        except (binascii.Error, UnicodeDecodeError, ValueError):
            if ':' in userinfo_raw:
                method, password = userinfo_raw.split(':', 1)
            else:
                raise ValueError(f"Could not parse method:password from userinfo '{userinfo_raw}' in {link}")

    if method is None or password is None:
        raise ValueError(f"Could not extract method/password for SS link: {link}. Userinfo: '{userinfo_raw}'")

    return {
        'original_link': link, 'protocol': 'shadowsocks', 'method': method, 'password': password,
        'host': host, 'port': int(port), 'network': 'tcp', 'name': name
    }


def generate_config(s_info, l_port):
    cfg = {
        "log": {"access": None, "error": None, "loglevel": "warning"},
        "inbounds": [{
            "port": l_port, "listen": "127.0.0.1", "protocol": "socks",
            "settings": {"auth": "noauth", "udp": True, "ip": "127.0.0.1"},
            "sniffing": {"enabled": True, "destOverride": ["http", "tls"]}
        }],
        "outbounds": [{
            "protocol": s_info['protocol'], "settings": {},
            "streamSettings": {
                "network": s_info.get('network', 'tcp'),
                "security": s_info.get('security', 'none')
            },
            "mux": {"enabled": True, "concurrency": 8}
        }]
    }
    out_s = cfg['outbounds'][0]['settings']
    stream_s = cfg['outbounds'][0]['streamSettings']

    if s_info['protocol'] == 'vless':
        out_s["vnext"] = [{"address": s_info['host'], "port": s_info['port'], "users": [
            {"id": s_info['uuid'], "encryption": s_info.get('encryption', 'none'), "flow": s_info.get('flow', '')}]}]
    elif s_info['protocol'] == 'vmess':
        out_s["vnext"] = [{"address": s_info['host'], "port": s_info['port'], "users": [
            {"id": s_info['uuid'], "alterId": s_info.get('alter_id', 0),
             "security": s_info.get('encryption', 'auto')}]}]
    elif s_info['protocol'] == 'trojan':
        out_s["servers"] = [{"address": s_info['host'],
                             "port": s_info['port'], "password": s_info['password']}]
    elif s_info['protocol'] == 'shadowsocks':
        out_s["servers"] = [{"address": s_info['host'], "port": s_info['port'],
                             "method": s_info['method'], "password": s_info['password'], "ota": False}]

    current_security = stream_s.get('security', 'none')
    if current_security == 'tls':
        tls_settings = {"serverName": s_info.get('sni', s_info['host']), "allowInsecure": True}
        if s_info.get('alpn'):
            tls_settings["alpn"] = s_info['alpn']
        if s_info.get('fp') and s_info.get('fp') not in ['none', '']:
            tls_settings["fingerprint"] = s_info['fp']
        stream_s['tlsSettings'] = tls_settings
    elif current_security == 'reality':
        if not s_info.get('pbk') or not s_info.get('fp'):
            raise ValueError("REALITY config missing 'pbk' (publicKey) or 'fp' (fingerprint)")
        stream_s['realitySettings'] = {
            "show": False, "fingerprint": s_info['fp'],
            "serverName": s_info.get('sni', s_info['host']),
            "publicKey": s_info['pbk'],
            "shortId": s_info.get('sid', ''),
            "spiderX": s_info.get('spx', '/')
        }

    current_network = stream_s.get('network', 'tcp')
    if current_network == 'ws':
        stream_s['wsSettings'] = {
            "path": s_info.get('ws_path', '/'),
            "headers": {"Host": s_info.get('ws_host', s_info.get('sni', s_info['host']))}
        }

    if stream_s.get('security') == 'none':
        stream_s.pop('security', None)
        stream_s.pop('tlsSettings', None)
        stream_s.pop('realitySettings', None)

    cfg['outbounds'][0]['streamSettings'] = {
        k: v for k, v in stream_s.items() if v is not None or k in ('network')
    }

    if stream_s.get('network', 'tcp') == 'tcp' and not any(k.endswith('Settings') for k in stream_s):
        cfg['outbounds'][0].pop('streamSettings', None)

    return cfg


def test_server(s_info, cfg, l_port, log_q):
    proc = None
    cfg_path = None
    success = False
    err_msg = "Test incomplete"
    r_time = -1.0
    try:
        V2RAY_DIR.mkdir(exist_ok=True)
        v2_exec = V2RAY_DIR / V2RAY_BIN
        if not v2_exec.exists():
            raise FileNotFoundError(f"V2Ray executable not found: {v2_exec}")
        if platform.system() != "Windows" and not os.access(v2_exec, os.X_OK):
            try:
                os.chmod(v2_exec, 0o755)
            except Exception as e:
                raise PermissionError(f"V2Ray chmod failed: {e}")

        with tempfile.NamedTemporaryFile(mode='w', delete=False, suffix='.json', encoding='utf-8', dir=V2RAY_DIR) as f:
            json.dump(cfg, f, indent=2)
            cfg_path = Path(f.name)

        cmd = [str(v2_exec), 'run', '--config', str(cfg_path)]
        proc = subprocess.Popen(cmd, cwd=V2RAY_DIR, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                encoding='utf-8', errors='ignore',
                                close_fds=(platform.system() != 'Windows'))

        time.sleep(2)
        if proc.poll() is not None:
            stderr_output = proc.stderr.read(500) if proc.stderr else ""
            raise RuntimeError(
                f"V2Ray exited prematurely (code {proc.returncode}). Stderr: {stderr_output[:200]}...")

        proxies = {'http': f'socks5h://127.0.0.1:{l_port}',
                   'https': f'socks5h://127.0.0.1:{l_port}'}
        start_t_req = time.monotonic()
        try:
            resp = requests.get(TEST_LINK, proxies=proxies, timeout=REQUEST_TIMEOUT,
                                verify=False, headers={'User-Agent': 'ProxyTester/1.0'})
            r_time = time.monotonic() - start_t_req
            if resp.status_code == 200:
                success = True
                err_msg = f"{resp.status_code} OK"
            else:
                err_msg = f"HTTP Status {resp.status_code}"
        except requests.exceptions.Timeout:
            r_time = time.monotonic() - start_t_req
            err_msg = f"Request Timeout ({r_time:.1f}s > {REQUEST_TIMEOUT}s)"
        except requests.exceptions.ProxyError as pe:
            err_msg = f"Proxy Error: {str(pe)[:100]}"
        except requests.exceptions.RequestException as e:
            err_msg = f"Request Exception: {str(e)[:100]}"

        log_level = logging.INFO if success else logging.WARNING
        log_symbol = "✅" if success else "⚠️"
        display_link = s_info.get('original_link', 'N/A')
        if len(display_link) > 70:
            display_link = display_link[:67] + "..."
        logging.log(log_level, f"{log_symbol} Test {'Success' if success else 'Failed'} ({r_time:.2f}s) - "
                    f"{s_info.get('protocol')} {s_info.get('host')}:{s_info.get('port')} | {err_msg} | Link: {display_link}")

    except Exception as e:
        err_msg = f"Test Setup/Runtime Error: {str(e)[:150]}"
        logging.error(f"❌ Error testing {s_info.get('host', 'N/A')} ({s_info.get('original_link', 'N/A')[:30]}...): {err_msg}",
                      exc_info=logger.isEnabledFor(logging.DEBUG))

    finally:
        if proc and proc.poll() is None:
            try:
                proc.terminate()
                proc.wait(timeout=3)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait(timeout=2)
            except Exception:
                pass
        if cfg_path and cfg_path.exists():
            try:
                cfg_path.unlink()
            except Exception:
                pass
        log_q.put(('success' if success else 'failure', s_info, f"{r_time:.2f}s" if success else err_msg))


def check_v2ray_installed():
    v2ray_path = V2RAY_DIR / V2RAY_BIN
    if not v2ray_path.exists():
        logging.debug("V2Ray executable not found.")
        return None
    try:
        if platform.system() != "Windows" and not os.access(v2ray_path, os.X_OK):
            logging.warning(f"V2Ray found but not executable, attempting chmod: {v2ray_path}")
            try:
                os.chmod(v2ray_path, 0o755)
            except Exception as chmod_err:
                logging.error(f"Failed to make V2Ray executable: {chmod_err}")
                return None

        result = subprocess.run([str(v2ray_path), 'version'], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                encoding='utf-8', check=True, cwd=V2RAY_DIR)
        output = result.stdout.strip()
        match = re.search(r'V2Ray\s+([\d.]+)', output)
        return match.group(1) if match else "unknown"
    except FileNotFoundError:
        logging.debug("V2Ray command failed: File not found.")
        return None
    except subprocess.CalledProcessError as e:
        logging.error(f"V2Ray version error {e.returncode}. Stderr: {e.stderr}")
        return None
    except Exception as e:
        logging.error(f"Unexpected V2Ray version check error: {e}")
        return None


_latest_release_data_cache = None
_cache_lock = threading.Lock()
_cache_time = 0
CACHE_DURATION = 300  # 5 minutes


def get_github_latest_release_data(force_refresh=False):
    global _latest_release_data_cache, _cache_time
    with _cache_lock:
        if not force_refresh and _latest_release_data_cache and (time.time() - _cache_time < CACHE_DURATION):
            logging.debug("Using cached GitHub release data.")
            return _latest_release_data_cache
        try:
            logging.debug("Fetching latest V2Ray release data from GitHub API...")
            response = requests.get('https://api.github.com/repos/v2fly/v2ray-core/releases/latest', timeout=15)
            response.raise_for_status()
            _latest_release_data_cache = response.json()
            _cache_time = time.time()
            logging.debug("Successfully fetched and cached GitHub release data.")
            return _latest_release_data_cache
        except requests.exceptions.RequestException as e:
            logging.error(f"Failed to fetch latest release data from GitHub: {e}")
            if _latest_release_data_cache:
                logging.warning("Returning stale GitHub cache due to fetch error.")
                return _latest_release_data_cache
            return None
        except Exception as e:
            logging.error(f"Unexpected error fetching/parsing GitHub release data: {e}")
            if _latest_release_data_cache:
                logging.warning("Returning stale GitHub cache due to unexpected error.")
                return _latest_release_data_cache
            return None


def get_latest_version():
    data = get_github_latest_release_data()
    if data:
        tag_name = data.get('tag_name')
        if tag_name and tag_name.startswith('v'):
            return tag_name.lstrip('v')
        logging.warning(f"Could not find valid tag_name in GitHub API response: {tag_name}")
    return None


def asset_name_exists(asset_name):
    data = get_github_latest_release_data()
    if data is None:
        return False
    return any(a.get('name') == asset_name for a in data.get('assets', []))


def get_asset_download_url(asset_name):
    data = get_github_latest_release_data()
    if data is None:
        return None
    for asset in data.get('assets', []):
        if asset.get('name') == asset_name:
            return asset.get('browser_download_url')
    logging.warning(f"Asset '{asset_name}' not found in release assets.")
    return None


def install_v2ray():
    try:
        os_type = platform.system().lower()
        machine = platform.machine().lower()
        logging.info(f"Detected OS: {os_type}, Machine: {machine}")
        asset_name = None
        if os_type == 'linux':
            if 'aarch64' in machine or 'arm64' in machine:
                asset_name = 'v2ray-linux-arm64-v8a.zip'
            elif 'armv7' in machine:
                asset_name = 'v2ray-linux-arm32-v7a.zip'
            elif '64' in machine:
                asset_name = 'v2ray-linux-64.zip'
            else:
                asset_name = 'v2ray-linux-32.zip'
        elif os_type == 'windows':
            if '64' in machine:
                asset_name = 'v2ray-windows-64.zip'
            else:
                asset_name = 'v2ray-windows-32.zip'
        if not asset_name:
            logging.critical(f"Unsupported OS/Architecture: {os_type}/{machine}")
            sys.exit(1)
        logging.info(f"Determined V2Ray asset: {asset_name}")

        if not asset_name_exists(asset_name):
            logging.info(f"Asset {asset_name} not found, forcing GitHub cache refresh.")
            get_github_latest_release_data(force_refresh=True)
            if not asset_name_exists(asset_name):
                logging.critical(f"Asset {asset_name} still not found after cache refresh. Check V2Fly releases.")
                sys.exit(1)

        download_url = get_asset_download_url(asset_name)
        if not download_url:
            logging.critical(f"Could not find download URL for {asset_name}.")
            sys.exit(1)

        logging.info(f"Downloading V2Ray from: {download_url}")
        V2RAY_DIR.mkdir(parents=True, exist_ok=True)
        clean_directory(V2RAY_DIR)
        V2RAY_DIR.mkdir(exist_ok=True)

        zip_path = V2RAY_DIR / "v2ray_download.zip"
        with requests.get(download_url, stream=True, timeout=300) as r:
            r.raise_for_status()
            with open(zip_path, 'wb') as f:
                for chunk in r.iter_content(chunk_size=8192):
                    f.write(chunk)
        logging.info(f"Downloaded V2Ray archive to {zip_path}")

        with zipfile.ZipFile(zip_path, 'r') as zip_ref:
            zip_ref.extractall(V2RAY_DIR)
        logging.info("Extraction complete.")

        zip_path.unlink()
        logging.debug(f"Removed V2Ray archive: {zip_path}")

        v2ray_executable_path = V2RAY_DIR / V2RAY_BIN
        if not v2ray_executable_path.exists():
            found_exe = False
            for root, _, files in os.walk(V2RAY_DIR):
                if V2RAY_BIN in files:
                    potential_exe_path = Path(root) / V2RAY_BIN
                    if potential_exe_path.parent != V2RAY_DIR:
                        logging.info(f"Moving V2Ray components from {potential_exe_path.parent} to {V2RAY_DIR}")
                        shutil.move(str(potential_exe_path), str(v2ray_executable_path))
                        for dat_file in ['geoip.dat', 'geosite.dat']:
                            src_dat = Path(root) / dat_file
                            dst_dat = V2RAY_DIR / dat_file
                            if src_dat.exists() and not dst_dat.exists():
                                shutil.move(str(src_dat), str(dst_dat))
                    found_exe = True
                    break
            if not found_exe:
                raise FileNotFoundError(f"V2Ray executable '{V2RAY_BIN}' not found in {V2RAY_DIR} after extraction.")

        if platform.system() != 'Windows' and v2ray_executable_path.exists():
            logging.info(f"Setting executable permission for {v2ray_executable_path}")
            os.chmod(v2ray_executable_path, 0o755)

        installed_version = check_v2ray_installed()
        if installed_version:
            logging.info(f"✅ V2Ray installation successful. Version: {installed_version}")
        else:
            raise RuntimeError("V2Ray installed but version check failed.")
    except (zipfile.BadZipFile, requests.exceptions.RequestException) as download_err:
        logging.critical(f"Download or extraction failed: {download_err}")
        clean_directory(V2RAY_DIR)
        sys.exit(1)
    except Exception as e:
        logging.critical(f"V2Ray installation failed: {e}", exc_info=True)
        clean_directory(V2RAY_DIR)
        sys.exit(1)


def print_real_time_channel_stats_table(stats_data):
    if not stats_data:
        return
    logging.info("\n--- Real-time Channel Test Statistics ---")
    header = f"{'Channel File/URL':<45} | {'Total':<7} | {'Active':<7} | {'Failed':<7} | {'Skip':<5} | {'Tested':<10} | {'Success%':<8}"
    logging.info(header)
    logging.info("-" * len(header))
    sorted_channels_list = sorted(stats_data.items(), key=lambda item: item[0])
    for channel_filename, stats in sorted_channels_list:
        base_channel_name = Path(channel_filename).stem
        display_name = f"https://t.me/s/{base_channel_name}" if base_channel_name.replace('_', '').isalnum() and not any(
            c in base_channel_name for c in ['/', '\\', '.']) else channel_filename
        total_prepared = stats['total_prepared']
        active = stats['active']
        failed = stats['failed']
        skip = stats['skip']
        processed_for_channel = active + failed + skip
        active_plus_failed = active + failed
        success_percent = (active / active_plus_failed * 100) if active_plus_failed > 0 else 0.0
        logging.info(
            f"{display_name:<45} | {total_prepared:<7} | {active:<7} | {failed:<7} | {skip:<5} | {processed_for_channel:>3}/{total_prepared:<3}    | {success_percent:>7.1f}%")
    logging.info("--- End Real-time ---")


def sort_server_file_by_time(file_path: Path):
    """Sorts a server file by test time. Assumes lines are 'link | X.YYs' for sortable entries."""
    if not file_path.exists() or file_path.stat().st_size == 0:
        logging.debug(f"Skipping sorting for empty or non-existent file: {file_path}")
        return
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            lines = f.readlines()
        parsed_lines_data = []
        for line_content in lines:
            stripped_content = line_content.strip()
            if not stripped_content:
                parsed_lines_data.append((float('inf'), line_content))
                continue
            parts = stripped_content.rsplit('|', 1)
            time_val = float('inf')
            if len(parts) == 2:
                potential_time_str = parts[1].strip()
                if potential_time_str.endswith('s') and not potential_time_str.lower().startswith('reason:'):
                    time_figure_str = potential_time_str[:-1]
                    try:
                        time_val = float(time_figure_str)
                    except ValueError:
                        logging.debug(f"Could not parse time from '{time_figure_str}' in {file_path}: '{stripped_content}'")
                        pass
            parsed_lines_data.append((time_val, line_content))
        parsed_lines_data.sort(key=lambda x: x[0])
        with open(file_path, 'w', encoding='utf-8') as f:
            for _, line_to_write in parsed_lines_data:
                f.write(line_to_write)
        logging.info(f"Successfully sorted file by test time: {file_path}")
    except Exception as e:
        logging.error(f"Error sorting file {file_path}: {e}", exc_info=True)


def logger_thread(log_q):
    global channel_test_stats
    protocols_dir = TESTED_SERVERS_DIR / 'Protocols'
    tested_channels_dir = TESTED_SERVERS_DIR / 'Channels'
    protocols_dir.mkdir(exist_ok=True)
    tested_channels_dir.mkdir(exist_ok=True)
    working_file = TESTED_SERVERS_DIR / 'working_servers.txt'
    dead_file = TESTED_SERVERS_DIR / 'dead_servers.txt'
    counts = {'success': 0, 'failure': 0, 'skip': 0, 'received': 0}
    protocol_success_counts = defaultdict(int)
    processed_since_last_rt_update = 0
    channel_stats_file = LOGS_DIR / "channel_stats.log"

    try:
        with open(working_file, 'w', encoding='utf-8') as wf, \
                open(dead_file, 'w', encoding='utf-8') as df:
            start_t = time.monotonic()
            total_to_process = 0
            while True:
                try:
                    record = log_q.get(timeout=3.0)
                except queue.Empty:
                    if total_to_process > 0 and sum(counts[s] for s in ['success', 'failure', 'skip']) < total_to_process:
                        prog_processed = sum(counts[s] for s in ['success', 'failure', 'skip'])
                        prog_elapsed = time.monotonic() - start_t
                        prog_percent = (prog_processed / total_to_process * 100) if total_to_process else 0
                        logging.info(
                            f"⏳ Overall Progress: {prog_processed}/{total_to_process} ({prog_percent:.1f}%) | Time: {prog_elapsed:.1f}s")
                        if channel_test_stats:
                            print_real_time_channel_stats_table(channel_test_stats)
                    continue

                if record is None:
                    logging.info("Logger thread: stop signal received. Finishing up writing files.")
                    break

                status, s_info, msg = record
                if status == 'received':
                    counts['received'] += 1
                    total_to_process = counts['received']
                    continue

                link = s_info.get('original_link', 'N/A')
                proto = s_info.get('protocol', 'unknown').lower()
                source_ch_file = s_info.get('source_file', 'unknown_channel.txt')

                if status in counts:
                    counts[status] += 1
                if status == 'success':
                    protocol_success_counts[proto] += 1

                if source_ch_file != 'unknown_channel.txt' and source_ch_file in channel_test_stats:
                    if status == 'success':
                        channel_test_stats[source_ch_file]['active'] += 1
                    elif status == 'failure':
                        channel_test_stats[source_ch_file]['failed'] += 1
                    elif status == 'skip':
                        channel_test_stats[source_ch_file]['skip'] += 1

                try:
                    if status == 'success':
                        wf.write(f"{link} | {msg}\n")
                        wf.flush()
                        with open(protocols_dir / f"{proto}.txt", 'a', encoding='utf-8') as pf:
                            pf.write(f"{link} | {msg}\n")
                        if source_ch_file != 'unknown_channel.txt':
                            with open(tested_channels_dir / source_ch_file, 'a', encoding='utf-8') as cf:
                                cf.write(f"{link} | {msg}\n")
                    elif status == 'failure':
                        df.write(f"{link} | Reason: {msg}\n")
                        df.flush()
                except Exception as e:
                    logging.error(f"Error writing to output file for {link}: {e}")

                processed_count_overall = sum(counts[s] for s in ['success', 'failure', 'skip'])
                processed_since_last_rt_update += 1
                if processed_since_last_rt_update >= REALTIME_UPDATE_INTERVAL or processed_count_overall == total_to_process:
                    if total_to_process > 0 and channel_test_stats:
                        prog_elapsed = time.monotonic() - start_t
                        prog_percent = (processed_count_overall / total_to_process * 100) if total_to_process else 0.0
                        logging.info(
                            f"⏳ Overall Progress: {processed_count_overall}/{total_to_process} ({prog_percent:.1f}%) | "
                            f"Active: {counts['success']} | Failed: {counts['failure']} | Skipped: {counts['skip']} | "
                            f"Time: {prog_elapsed:.1f}s")
                        print_real_time_channel_stats_table(channel_test_stats)
                        processed_since_last_rt_update = 0

    except Exception as e:
        logging.critical(f"Critical error in logger thread's main loop: {e}", exc_info=True)
    finally:
        try:
            with open(channel_stats_file, 'w', encoding='utf-8') as f:
                f.write("Channel Statistics Report (Testing Phase)\n")
                f.write("Summary per channel (Final State):\n")
                f.write("Channel                                       | Total  | Active | Failed | Success%\n")
                ranked_channels_for_file = []
                for ch_filename, stats in channel_test_stats.items():
                    base_ch_name = Path(ch_filename).stem
                    display_name = f"https://t.me/s/{base_ch_name}" if base_ch_name.replace('_', '').isalnum() and not any(
                        c in base_ch_name for c in ['/', '\\', '.']) else ch_filename
                    total = stats['total_prepared']
                    active = stats['active']
                    failed = stats['failed']
                    success_percent = (active / (active + failed) * 100) if (active + failed) > 0 else 0.0
                    ranked_channels_for_file.append((display_name, total, active, failed, success_percent))

                ranked_channels_for_file.sort(key=lambda x: (-x[4], -x[2], x[0]))
                for entry in ranked_channels_for_file:
                    f.write(f"{entry[0].ljust(45)} | {str(entry[1]).ljust(6)} | {str(entry[2]).ljust(6)} | {str(entry[3]).ljust(6)} | {entry[4]:>6.1f}%\n")
            logging.info(f"📊 Channel testing statistics saved to {channel_stats_file}")
        except Exception as e:
            logging.error(f"❌ Error writing channel testing stats to file {channel_stats_file}: {e}")

        logging.info("--- Sorting working server files by test time ---")
        sort_server_file_by_time(working_file)
        if protocols_dir.exists():
            for filename in protocols_dir.iterdir():
                if filename.suffix == '.txt':
                    sort_server_file_by_time(filename)
        if tested_channels_dir.exists():
            for filename in tested_channels_dir.iterdir():
                if filename.suffix == '.txt':
                    sort_server_file_by_time(filename)
        logging.info("--- File sorting complete ---")

        logging.info("\n" + "=" * 20 + " Testing Summary " + "=" * 20)
        total_tested_final = sum(counts[s] for s in ['success', 'failure', 'skip'])
        logging.info(f"Total Servers Received for Testing: {counts['received']}")
        logging.info(f"Total Servers Processed (Tested/Skipped): {total_tested_final}")
        logging.info(f"  ✅ Active:   {counts['success']}")
        logging.info(f"  ❌ Failed:   {counts['failure']}")
        logging.info(f"  ➖ Skipped:  {counts['skip']}")
        logging.info("-" * 50 + "\nActive Servers by Protocol:")
        if protocol_success_counts:
            for p, c in sorted(protocol_success_counts.items(), key=lambda item: item[1], reverse=True):
                logging.info(f"  {p.upper():<10}: {c}")
        else:
            logging.info("  (No servers active by protocol)")

        logging.info("\n" + "=" * 20 + " Channel Statistics Report (Final Ranking by Success Rate - Console) " + "=" * 20)
        final_header = f"{'Channel File/URL':<45} | {'Total':<7} | {'Active':<7} | {'Failed':<7} | {'Skip':<5} | {'Success%':<8}"
        logging.info(final_header)
        logging.info("-" * len(final_header))
        ranked_channels_summary = []
        if channel_test_stats:
            for ch_filename, stats in channel_test_stats.items():
                base_ch_name = Path(ch_filename).stem
                display_name = f"https://t.me/s/{base_ch_name}" if base_ch_name.replace('_', '').isalnum() and not any(
                    c in base_ch_name for c in ['/', '\\', '.']) else ch_filename
                active_plus_failed = stats['active'] + stats['failed']
                success_p = (stats['active'] / active_plus_failed * 100) if active_plus_failed > 0 else 0.0
                ranked_channels_summary.append({
                    'name': display_name, 'total': stats['total_prepared'],
                    'active': stats['active'], 'failed': stats['failed'],
                    'skip': stats['skip'], 'success_percent': success_p
                })
            sorted_final_ranking_summary = sorted(ranked_channels_summary, key=lambda x: (
                x['success_percent'], x['active'], -x['total'], x['name']), reverse=True)
            for entry in sorted_final_ranking_summary:
                logging.info(
                    f"{entry['name']:<45} | {entry['total']:<7} | {entry['active']:<7} | {entry['failed']:<7} | {entry['skip']:<5} | {entry['success_percent']:>7.1f}%")
        if not ranked_channels_summary:
            logging.info("  (No channel-specific test data for final ranking display)")
        logging.info("=" * len(final_header))
        logging.info(f"\nWorking servers saved to: {working_file} (sorted by test time)")
        logging.info(f"Protocol-specific working servers in: {protocols_dir} (sorted by test time)")
        logging.info(f"Channel-specific working servers in: {tested_channels_dir} (sorted by test time)")
        logging.info(f"Failed servers saved to: {dead_file}")
        logging.info("--- Logger thread finished ---")


def clean_vmess_links(directory: str):
    for root, _, files in os.walk(directory):
        for filename in files:
            if filename.endswith('.txt'):
                filepath = Path(root) / filename
                clean_single_file(filepath)


def clean_single_file(filepath: Path):
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            lines = f.readlines()
        cleaned_lines = []
        modified = False
        for line in lines:
            original_line = line.strip()
            if 'vmess://' in original_line:
                cleaned_line = original_line.split('|')[0].strip()
                if cleaned_line != original_line:
                    modified = True
                cleaned_lines.append(cleaned_line + '\n')
            else:
                cleaned_lines.append(line)
        if modified:
            with open(filepath, 'w', encoding='utf-8') as f:
                f.writelines(cleaned_lines)
            print(f'file {filepath} vmess cleaned')
        else:
            print(f'file {filepath} .')
    except Exception as e:
        print(f' error in {filepath}: {str(e)}')


def organize_tested_servers_by_region():
    """Reads the cleaned, working servers from Tested_Servers/Protocols and organizes them into
    Tested_Servers/Regions based on GeoIP analysis.
    This function should be called AFTER clean_vmess_links to ensure clean links.
    """
    TESTED_REGIONS_DIR = TESTED_SERVERS_DIR / 'Regions'
    if not GEOIP_DATABASE_PATH.exists() or GEOIP_DATABASE_PATH.stat().st_size < 1024 * 1024:
        logging.error("❌ Cannot organize by region: GeoIP database not found or invalid.")
        return

    geo_reader = None
    try:
        geo_reader = geoip2.database.Reader(str(GEOIP_DATABASE_PATH))
    except Exception as e:
        logging.error(f"❌ Error opening GeoIP DB for organizing tested servers: {e}")
        return

    country_configs = defaultdict(list)
    PROTOCOLS_DIR = TESTED_SERVERS_DIR / 'Protocols'

    if not PROTOCOLS_DIR.exists():
        logging.warning(f"Protocols directory not found: {PROTOCOLS_DIR}")
        if geo_reader:
            geo_reader.close()
        return

    for proto_file in PROTOCOLS_DIR.glob("*.txt"):
        logging.info(f"Reading working servers from: {proto_file}")
        try:
            with open(proto_file, 'r', encoding='utf-8') as f:
                for line in f:
                    link = line.strip()
                    if not link or link.startswith('#'):
                        continue

                    clean_link = link.split('|', 1)[0].strip()
                    ip_address = None
                    try:
                        parsed_link = urlparse(clean_link)
                        hostname = parsed_link.hostname
                        if not hostname:
                            continue

                        if parsed_link.scheme in ['vless', 'trojan', 'hysteria', 'hysteria2', 'tuic', 'ss']:
                            ip_address = hostname
                        elif parsed_link.scheme == 'vmess':
                            try:
                                b64_payload = parsed_link.netloc + parsed_link.path
                                decoded_payload = urlsafe_b64decode(b64_payload + '=' * ((4 - len(b64_payload) % 4) % 4)).decode('utf-8')
                                vmess_data = json.loads(decoded_payload)
                                ip_address = vmess_data.get('add')
                            except Exception:
                                continue
                    except Exception:
                        continue

                    if ip_address and re.match(r"^\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}$", ip_address):
                        try:
                            response = geo_reader.country(ip_address)
                            country_code = response.country.iso_code or "Unknown"
                        except geoip2.errors.AddressNotFoundError: # type: ignore
                            country_code = "Unknown"
                        except Exception:
                            country_code = "Unknown"
                    else:
                        country_code = "Unknown"

                    country_configs[country_code].append(line.strip())
        except Exception as e:
            logging.error(f"Error reading protocol file {proto_file}: {e}")

    if geo_reader:
        geo_reader.close()

    for country_code, config_list in country_configs.items():
        safe_country_name = "".join(c if c.isalnum() else "_" for c in country_code)
        output_file = TESTED_REGIONS_DIR / f"{safe_country_name}.txt"
        try:
            output_file.parent.mkdir(exist_ok=True)
            with open(output_file, 'w', encoding='utf-8') as f:
                f.write('\n'.join(config_list) + '\n')
            logging.info(f"Wrote {len(config_list)} tested servers to {output_file}")
        except Exception as e:
            logging.error(f"Error writing region file for {country_code}: {e}")

    logging.info("✅ Organization of tested servers by region is complete.")


if __name__ == "__main__":
    logging.info("--- Starting Part 1: Telegram Channel Scraping ---")
    try:
        if not CHANNELS_FILE.exists():
            logging.error(f"Telegram sources file not found: {CHANNELS_FILE}")
            sys.exit(1)
        with open(CHANNELS_FILE, 'r', encoding='utf-8') as f:
            raw_urls = [line.strip() for line in f if line.strip() and not line.strip().startswith('#')]
        normalized_urls = []
        for url in raw_urls:
            norm_url = normalize_telegram_url(url)
            if norm_url and norm_url not in normalized_urls:
                normalized_urls.append(norm_url)
        normalized_urls.sort()
        logging.info(f"✅ Found {len(normalized_urls)} unique, normalized Telegram channels to process.")
    except Exception as e:
        logging.error(f"❌ Error processing Telegram channel list ({CHANNELS_FILE}): {e}")
        sys.exit(1)

    total_channels_count = len(normalized_urls)
    processed_ch_count = 0
    total_new_added = 0
    failed_fetches = 0
    for idx, ch_url in enumerate(normalized_urls, 1):
        logging.info(f"--- Processing Channel {idx}/{total_channels_count}: {ch_url} ---")
        success_flag, new_srvs = process_channel(ch_url)
        if success_flag == 1:
            processed_ch_count += 1
            total_new_added += new_srvs
        else:
            failed_fetches += 1
        if idx % BATCH_SIZE == 0 and idx < total_channels_count:
            logging.info(f"--- Batch of {BATCH_SIZE} processed, sleeping for {SLEEP_TIME}s ---")
            time.sleep(SLEEP_TIME)

    logging.info(f"--- Telegram Scraping Finished ---")
    logging.info(f"Successfully processed {processed_ch_count}/{total_channels_count} channels.")
    if failed_fetches > 0:
        logging.warning(f"{failed_fetches} channels failed during fetch/processing.")
    logging.info(f"Added {total_new_added} new unique servers globally from scraping.")

    logging.info("\n--- Starting Part 2: GeoIP Analysis ---")
    country_data_map = process_geo_data()
    if country_data_map:
        logging.info("✅ GeoIP analysis complete.")
    else:
        logging.warning("⚠️ GeoIP analysis did not return data or failed.")

    logging.info("\n--- Starting Part 3: Generating Extraction Report ---")
    try:
        extraction_channel_stats = get_channel_stats()
        save_extraction_data(extraction_channel_stats, country_data_map)
        logging.info("✅ Extraction report generated.")
    except Exception as e:
        logging.error(f"❌ Failed to generate extraction report: {e}")

    logging.info("\n--- Starting Part 4: Server Testing ---")
    logging.info(f"Cleaning previous test results in: {TESTED_SERVERS_DIR}...")
    clean_directory(TESTED_SERVERS_DIR)
    (TESTED_SERVERS_DIR / 'Protocols').mkdir(exist_ok=True)
    (TESTED_SERVERS_DIR / 'Channels').mkdir(exist_ok=True)

    all_servers_to_test = []
    servers_read_total = 0
    parsing_errors = defaultdict(int)
    proto_load_counts = defaultdict(int)
    skipped_disabled_count = 0

    if not CHANNELS_DIR.exists():
        logging.error(f"Source channels directory {CHANNELS_DIR} not found. Cannot load servers for testing.")
        sys.exit(1)
    source_channel_files = [f for f in os.listdir(CHANNELS_DIR) if f.endswith('.txt')]
    if not source_channel_files:
        logging.error(f"😐 No channel files in {CHANNELS_DIR} to test from. Ensure Part 1 ran successfully.")
        sys.exit(1)

    for ch_filename in source_channel_files:
        _ = channel_test_stats[ch_filename]
        servers_from_file = read_links_from_file(CHANNELS_DIR / ch_filename)
        servers_read_total += len(servers_from_file)
        for link_str in servers_from_file:
            try:
                parsed_url_scheme = urlparse(link_str).scheme.lower()
                if not parsed_url_scheme:
                    parsing_errors["no_scheme"] += 1
                    continue
                if parsed_url_scheme not in ENABLED_PROTOCOLS or not ENABLED_PROTOCOLS[parsed_url_scheme]:
                    if parsed_url_scheme not in ENABLED_PROTOCOLS:
                        parsing_errors[f"unsupported_{parsed_url_scheme}"] += 1
                    else:
                        parsing_errors["disabled_protocol"] += 1
                        skipped_disabled_count += 1
                    continue
                server_info_dict = None
                parser_func = {
                    'vless': parse_vless_link,
                    'vmess': parse_vmess_link,
                    'trojan': parse_trojan_link,
                    'ss': parse_ss_link
                }.get(parsed_url_scheme)
                if parser_func:
                    try:
                        server_info_dict = parser_func(link_str)
                    except ValueError as ve:
                        parsing_errors[f"parse_invalid_{parsed_url_scheme}"] += 1
                        logging.debug(f"Invalid {parsed_url_scheme} link in {ch_filename} ({ve}): {link_str[:60]}...")
                    except Exception as pe_inner:
                        parsing_errors[f"parse_general_error_{parsed_url_scheme}"] += 1
                        logging.warning(
                            f"General parsing error for {parsed_url_scheme} link in {ch_filename} ({type(pe_inner).__name__}: {pe_inner}): {link_str[:60]}...")
                else:
                    parsing_errors[f"no_parser_for_enabled_{parsed_url_scheme}"] += 1
                    logging.error(f"Logic error: No parser for enabled protocol {parsed_url_scheme}")
                if server_info_dict:
                    server_info_dict['source_file'] = ch_filename
                    all_servers_to_test.append(server_info_dict)
                    proto_load_counts[parsed_url_scheme] += 1
                    channel_test_stats[ch_filename]['total_prepared'] += 1
            except Exception as outer_ex:
                parsing_errors["outer_processing_loop"] += 1
                logging.warning(
                    f"Outer error processing link line from {ch_filename} ({type(outer_ex).__name__}: {outer_ex}): {link_str[:60]}...")

    logging.info(f"Read {servers_read_total} links. Prepared {len(all_servers_to_test)} for testing.")
    if skipped_disabled_count > 0:
        logging.info(f"Skipped {skipped_disabled_count} servers due to disabled protocols.")
    if parsing_errors:
        logging.warning("Parsing issues encountered while loading servers for test:")
        for err_type, count_val in parsing_errors.items():
            logging.warning(f"  - {err_type}: {count_val}")
    if not all_servers_to_test:
        logging.error("❌ No valid and enabled servers found to test after parsing. Exiting.")
        sys.exit(1)

    parser = argparse.ArgumentParser(description="Scrape Telegram for proxies and test them.")
    parser.add_argument('--max-threads', type=int, default=MAX_THREADS, help=f"Max testing threads (default: {MAX_THREADS})")
    parser.add_argument('--skip-install', action='store_true', help="Skip V2Ray check and installation.")
    cli_args = parser.parse_args()
    MAX_THREADS = cli_args.max_threads

    logging.info("\n--- V2Ray Check ---")
    if not cli_args.skip_install:
        installed_ver = check_v2ray_installed()
        latest_ver = get_latest_version()
        logging.info(f"Installed V2Ray version: {installed_ver or 'Not found'}")
        logging.info(f"Latest V2Ray version (GitHub): {latest_ver or 'Could not fetch'}")
        if not installed_ver or (latest_ver and installed_ver != latest_ver and installed_ver != "unknown"):
            logging.info("🚀 Attempting V2Ray installation/update...")
            install_v2ray()
            installed_ver = check_v2ray_installed()
            if not installed_ver:
                logging.critical("V2Ray install attempted but still not found. Exiting.")
                sys.exit(1)
            logging.info(f"Using V2Ray version after install/update: {installed_ver}")
        else:
            logging.info(f"✅ Using existing V2Ray version: {installed_ver}")
    else:
        logging.warning("Skipping V2Ray check and installation as requested (--skip-install).")
        current_v2_ver = check_v2ray_installed()
        if not current_v2_ver:
            logging.error("V2Ray check skipped, but V2Ray not found/working. Testing cannot proceed.")
            sys.exit(1)
        else:
            logging.info(f"Confirmed V2Ray is present (version: {current_v2_ver}) despite skipping install check.")

    logging.info(f"\n--- Starting Server Testing ({len(all_servers_to_test)} servers, {MAX_THREADS} threads) ---")
    test_log_queue = queue.Queue()
    logger_t = threading.Thread(target=logger_thread, args=(test_log_queue,), name="LoggerThread", daemon=True)
    logger_t.start()

    for s_info_item in all_servers_to_test:
        test_log_queue.put(('received', s_info_item, None))

    with ThreadPoolExecutor(max_workers=MAX_THREADS, thread_name_prefix="Tester") as executor:
        futures_list = []
        for s_info_item in all_servers_to_test:
            try:
                local_port = get_next_port()
                config_data = generate_config(s_info_item, local_port)
                futures_list.append(executor.submit(test_server, s_info_item, config_data, local_port, test_log_queue))
            except Exception as e_prep:
                logging.error(
                    f"❌ Error preparing test (e.g., config gen) for {s_info_item.get('original_link', 'N/A')[:60]}...: {e_prep}")
                s_info_item['source_file'] = s_info_item.get('source_file', 'unknown_channel.txt')
                test_log_queue.put(('skip', s_info_item, f"Prep error: {str(e_prep)[:100]}"))

        logging.info(f"Submitted {len(futures_list)} testing tasks. Waiting for completion...")
        for fut_idx, fut in enumerate(futures_list):
            try:
                fut.result()
            except Exception as fe_task:
                logging.error(f"A testing task future (idx {fut_idx}) failed unexpectedly: {fe_task}", exc_info=False)

    tested_servers_dir = str(TESTED_SERVERS_DIR)
    clean_vmess_links(tested_servers_dir)
    print('all vmess time cleaned')
    organize_tested_servers_by_region()

    logging.info("All testing tasks submitted and completed by executor. Signaling logger thread to finalize.")
    test_log_queue.put(None)
    logger_t.join(timeout=30)
    if logger_t.is_alive():
        logging.warning("Logger thread did not exit cleanly after timeout. Stats might be incomplete in console/log.")
    logging.info("--- Testing Phase Complete ---")
    logging.info("--- Script Finished ---")
