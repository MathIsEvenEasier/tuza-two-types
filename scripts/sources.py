#!/usr/bin/env python3
"""Fetch and hash-check the complete source package. Does not run Lean."""
import argparse, hashlib, json, pathlib, re, tarfile, urllib.request
ROOT = pathlib.Path(__file__).resolve().parents[1]
def digest(path):
    h=hashlib.sha256()
    with pathlib.Path(path).open('rb') as f:
        for block in iter(lambda:f.read(1048576),b''): h.update(block)
    return h.hexdigest()
def prepare(destination, asset_dir=None):
    destination=pathlib.Path(destination); destination.mkdir(parents=True,exist_ok=False)
    manifest=json.loads((ROOT/'certificates/source-manifest.json').read_text())
    assets=pathlib.Path(asset_dir) if asset_dir else ROOT/'.downloads'
    assets.mkdir(exist_ok=True)
    seen=set()
    for entry in manifest['modules']:
        if 'path' not in entry: continue
        source=ROOT/entry['path']
        if digest(source)!=entry['sha256']: raise ValueError('Source hash mismatch: '+entry['module'])
        (destination/(entry['module']+'.lean')).write_bytes(source.read_bytes());seen.add(entry['module'])
    for entry in manifest['assets']:
        archive=assets/entry['file']
        if not archive.exists():
            temporary=archive.with_suffix('.part')
            with urllib.request.urlopen(entry['url'],timeout=60) as src,temporary.open('wb') as out:
                count=0
                while True:
                    block=src.read(1048576)
                    if not block:break
                    count+=len(block)
                    if count>entry['bytes']:raise ValueError('Download exceeds declared size')
                    out.write(block)
            temporary.rename(archive)
        if archive.stat().st_size!=entry['bytes'] or digest(archive)!=entry['sha256']:
            raise ValueError('Archive hash mismatch: '+entry['file'])
        wanted={r['module']:r for r in manifest['modules'] if r.get('asset')==entry['file']}
        extracted=set()
        with tarfile.open(archive,'r|gz') as tf:
            for member in tf:
                if not member.isfile() or member.issparse() or not re.fullmatch(r'[A-Za-z0-9_]+\.lean',member.name):
                    raise ValueError('Invalid archive member')
                name=member.name[:-5]; rec=wanted.get(name)
                if rec is None or name in seen or member.size!=rec['bytes']:raise ValueError('Unexpected or duplicate source')
                data=tf.extractfile(member).read()
                if hashlib.sha256(data).hexdigest()!=rec['sha256']:raise ValueError('Source hash mismatch: '+name)
                (destination/member.name).write_bytes(data);seen.add(name);extracted.add(name)
        if extracted!=set(wanted):raise ValueError('Incomplete certificate archive')
    if seen!={r['module'] for r in manifest['modules']}:raise ValueError('Incomplete source bundle')
    print('Hash-checked all '+str(len(seen))+' source modules. No Lean compilation performed.',flush=True)
    return manifest
if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('destination');ap.add_argument('--assets')
    a=ap.parse_args();prepare(a.destination,a.assets)
