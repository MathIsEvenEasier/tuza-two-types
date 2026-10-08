"""Small, standard-library-only helpers shared by controller and Azure guest."""
import datetime as dt
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import ssl
import tarfile
import urllib.error
import urllib.parse
import urllib.request

# The python.org macOS build can lose its private CA bundle after a system
# update.  Keep certificate verification enabled by falling back to the
# current system trust bundle used by native tools.
if not ssl.get_default_verify_paths().cafile and Path('/etc/ssl/cert.pem').is_file():
    os.environ.setdefault('SSL_CERT_FILE', '/etc/ssl/cert.pem')

SUBSCRIPTION = os.environ.get('AZURE_SUBSCRIPTION_ID', '')
REGION = 'eastus'
VM_SIZE = 'Standard_E8as_v7'
IMAGE = 'Canonical:ubuntu-24_04-lts:server:24.04.202608270'
PINS = {'lean': '4.34.0', 'mathlib': '5ed2965256430c3649e86755f9576b54eca72435'}
SOURCES = {}
SCAN_JOBS = {}
GRAVER_JOBS = {}
EXACT_JOBS = {}
MAX_ARCHIVE = 256 * 1024**2
MAX_EXPANDED = 512 * 1024**2


class AuditError(RuntimeError):
    pass


def require(condition, message):
    if not condition:
        raise AuditError(message)


def utcnow():
    return dt.datetime.now(dt.timezone.utc)


def stamp(value=None):
    return (value or utcnow()).strftime('%Y-%m-%dT%H:%M:%SZ')


def parse_time(value):
    parsed = dt.datetime.fromisoformat(value.replace('Z', '+00:00'))
    require(parsed.tzinfo is not None, 'Timestamp needs a timezone')
    return parsed


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def write_json(path, value):
    path = Path(path)
    tmp = path.with_name(path.name + '.tmp')
    with os.fdopen(os.open(tmp, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600), 'w') as out:
        json.dump(value, out, indent=2)
        out.write('\n')
        out.flush()
        os.fsync(out.fileno())
    os.replace(tmp, path)


def read_json(path):
    return json.loads(Path(path).read_text())


def names(job_id):
    require(re.fullmatch(r'[0-9a-f]{16}', job_id), 'Invalid job ID')
    return {'compute_rg': f'mie-{job_id}-compute', 'control_rg': f'mie-{job_id}-control',
            'storage': f'mie{job_id}', 'workflow': 'deadline-cleanup'}


def tags(job_id):
    return {'managed-by': 'mathiseasy-azure-audit', 'job-id': job_id, 'purpose': 'public-lean-ci'}


def validate_state(state):
    require(state.get('schema') == 1, 'Unknown state schema')
    require(state.get('subscription') == SUBSCRIPTION, 'Unexpected subscription')
    require(state.get('names') == names(state['job_id']), 'Resource names do not match job ID')
    require(state.get('region') == REGION and state.get('vm_size') == VM_SIZE, 'Unexpected VM configuration')
    require(state.get('pins') == PINS, 'Changed toolchain pins')
    require(state.get('minutes') == 185, 'Unexpected deadline interval')
    require(all(state['files'].get(k) == v for k, v in SOURCES.items()), 'Changed audited sources')


def safe_extract(archive, destination, max_bytes=MAX_EXPANDED):
    """Flat regular files only; validate ALL headers before writing any member."""
    destination = Path(destination)
    require(not destination.exists(), 'Extraction destination already exists')
    with tarfile.open(archive, 'r:gz') as tf:
        members, seen, total = [], set(), 0
        for member in tf:
            name = member.name
            require(len(members) < 100, 'Too many archive members')
            require(member.isfile() and not member.issparse(), 'Non-regular archive member')
            require(PurePosixPath(name).name == name and name not in ('.', '..', ''), 'Unsafe archive path')
            require(re.fullmatch(r'[A-Za-z0-9_.-]+', name), 'Invalid archive name')
            require(name not in seen, 'Duplicate archive member')
            total += member.size
            require(0 <= member.size and total <= max_bytes, 'Archive expansion limit exceeded')
            seen.add(name)
            members.append(member)
        destination.mkdir(mode=0o700, parents=True)
        for member in members:
            with tf.extractfile(member) as src, (destination / member.name).open('xb') as dst:
                while block := src.read(1024 * 1024):
                    dst.write(block)


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args, **kwargs):
        return None


def blob_request(url, *, data=None, method='GET', limit=MAX_ARCHIVE, destination=None):
    """Never print SAS URLs or follow their redirects. Caller handles retries."""
    parsed = urllib.parse.urlsplit(url)
    require(parsed.scheme == 'https' and re.fullmatch(r'mie[0-9a-f]{16}\.blob\.core\.windows\.net', parsed.netloc)
            and parsed.path.startswith('/audit/'), 'Invalid blob endpoint')
    headers = {'x-ms-version': '2023-11-03'}
    if method == 'PUT':
        headers['x-ms-blob-type'] = 'BlockBlob'
    req = urllib.request.Request(url, data=data, method=method, headers=headers)
    try:
        with urllib.request.build_opener(NoRedirect).open(req, timeout=60) as response:
            if destination is None:
                result = response.read(limit + 1)
                require(len(result) <= limit, 'Blob response too large')
                return result
            size = 0
            with Path(destination).open('wb') as out:
                while chunk := response.read(1024 * 1024):
                    size += len(chunk)
                    require(size <= limit, 'Blob exceeds download limit')
                    out.write(chunk)
                out.flush()
                os.fsync(out.fileno())
    except urllib.error.HTTPError as exc:
        raise AuditError(f'Blob HTTP {exc.code}') from None
    except (OSError, urllib.error.URLError):
        raise AuditError('Blob transport failure (URL redacted)') from None
