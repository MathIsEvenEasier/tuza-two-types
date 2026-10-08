#!/usr/bin/env python3
"""Fresh project proof build; intended only for an independently bounded Azure runner."""
import gzip,hashlib,json,os,pathlib,re,shutil,subprocess,time,urllib.request
root=pathlib.Path(__file__).resolve().parents[1]
out=root/'ci-output';out.mkdir(exist_ok=False)
pin='5ed2965256430c3649e86755f9576b54eca72435'
started=time.monotonic()
def run(cmd,cwd=None,timeout=900,env=None,capture=False):
    p=subprocess.run(cmd,cwd=cwd or root,env=env,timeout=timeout,
        text=True,stdout=subprocess.PIPE if capture else None,stderr=subprocess.STDOUT)
    if p.returncode: raise RuntimeError('Command failed: '+cmd[0]+' (exit '+str(p.returncode)+')')
    return p.stdout if capture else None
if not pathlib.Path('/run/mathiseasy-azure-verified').is_file():
    raise SystemExit('A verified Azure worker with independent deletion guard is required')
cgroup=next(x.split(':',2)[2] for x in pathlib.Path('/proc/self/cgroup').read_text().splitlines() if x.startswith('0:'))
cap=(pathlib.Path('/sys/fs/cgroup')/cgroup.lstrip('/')/'memory.max').read_text().strip()
if cap=='max' or int(cap)>24*1024**3: raise SystemExit('Whole-job memory limit must be at most 24 GiB')
commit=run(['git','rev-parse','HEAD'],capture=True).strip()
if commit!=os.environ['GITHUB_SHA']: raise SystemExit('Checkout does not match the workflow commit')
if run(['git','status','--porcelain'],capture=True).strip(): raise SystemExit('Checkout is not clean')
provenance={'repository':os.environ['GITHUB_REPOSITORY'],'commit':commit,
 'run_url':'https://github.com/'+os.environ['GITHUB_REPOSITORY']+'/actions/runs/'+os.environ['GITHUB_RUN_ID'],
 'mathlib':pin,'lean':'4.34.0','memory_limit_bytes':int(cap),'status':'IN_PROGRESS'}
(out/'provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
print(json.dumps(provenance,indent=2),flush=True)
release=json.loads((root/'ci/lean-release.json').read_text())
cache=pathlib.Path('/opt/proof-cache');archive=cache/'lean.tar.zst'
if not archive.is_file(): urllib.request.urlretrieve(release['browser_download_url'],archive)
if hashlib.file_digest(archive.open('rb'),'sha256').hexdigest()!=release['digest'].split(':')[1]:
    raise SystemExit('Lean release hash mismatch')
if not (cache/'lean-4.34.0-linux').exists(): run(['tar','--zstd','-xf',str(archive),'-C',str(cache)])
os.environ['PATH']=str(cache/'lean-4.34.0-linux/bin')+':'+os.environ['PATH']
print('Lean release SHA-256 verified: '+release['digest'],flush=True)
work=pathlib.Path(os.environ['RUNNER_TEMP'])/'mathlib'
run(['git','init',str(work)])
run(['git','-C',str(work),'remote','add','origin','https://github.com/leanprover-community/mathlib4.git'])
run(['git','-C',str(work),'fetch','--depth','1','origin',pin])
run(['git','-C',str(work),'checkout','--detach','FETCH_HEAD'])
if run(['git','rev-parse','HEAD'],work,capture=True).strip()!=pin: raise SystemExit('Wrong mathlib commit')
version=run(['lean','--version'],work,capture=True).strip();print(version,flush=True)
if not version.startswith('Lean (version 4.34.0,'): raise SystemExit('Wrong Lean version')
imports=sorted(set(m for f in (root/'formal').glob('*.lean') for m in re.findall(r'^import (Mathlib\.[A-Za-z0-9_.]+)$',f.read_text(),re.M)))
run(['lake','exe','cache','get']+[m.replace('.','/')+'.lean' for m in imports],work,timeout=900)
try:
    run(['python3','-u',str(root/'scripts/rebuild.py'),str(work)],work,timeout=6200)
    report=json.loads((out/'rebuild-report.json').read_text())
    if report['status']!='VERIFIED' or report['modules']!=3190 or not report['negative_control_rejected']:
        raise RuntimeError('Incomplete source build')
    provenance.update(report)
except BaseException:
    provenance['status']='FAILED'
    raise
finally:
    provenance['seconds']=round(time.monotonic()-started,3)
    (out/'provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
    if os.environ.get('GITHUB_STEP_SUMMARY'):
        with open(os.environ['GITHUB_STEP_SUMMARY'],'a') as f:
            f.write('## Lean verification: '+provenance['status']+'\n\nCommit: `'+commit+'`\n\n')
            f.write('Lean 4.34.0; mathlib `'+pin+'`. All 3,190 project modules rebuilt from source.\n\n')
            if provenance['status']=='VERIFIED':f.write('Final theorem: `'+report['theorem']+'`\n\nAxioms: `'+', '.join(report['axioms'])+'`.\n')
    print('Build status: '+provenance['status'],flush=True)
