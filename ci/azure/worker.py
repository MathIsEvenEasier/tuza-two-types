"""Run one job per repository, sequentially, inside the parent's bounded cgroup."""
import hashlib,json,os,pathlib,shutil,subprocess,tarfile,time,urllib.request
root=pathlib.Path(__file__).resolve().parent
assert pathlib.Path('/run/mathiseasy-azure-verified').is_file()
registrations=json.loads((root/'registration.json').read_text())
subprocess.run(['useradd','--create-home','--shell','/bin/bash','proofci'],check=True)
cache=pathlib.Path('/opt/proof-cache');cache.mkdir()
subprocess.run(['chown','proofci:proofci',str(cache)],check=True)
archive=root/'runner.tar.gz'
urllib.request.urlretrieve('https://github.com/actions/runner/releases/download/v2.337.0/actions-runner-linux-x64-2.337.0.tar.gz',archive)
assert hashlib.file_digest(archive.open('rb'),'sha256').hexdigest()=='70920811a4f8ad4328818682bca5c6469c1c942fab52448868071d0063816613'
folders=[]
for reg in registrations:
    folder=pathlib.Path('/home/proofci')/reg['name'];folder.mkdir()
    subprocess.run(['tar','xzf',str(archive),'-C',str(folder)],check=True)
    subprocess.run(['chown','-R','proofci:proofci',str(folder)],check=True)
    env=dict(os.environ,ACTIONS_RUNNER_INPUT_TOKEN=reg['token'])
    cmd=['runuser','-u','proofci','--','./config.sh','--unattended',
         '--url','https://github.com/'+reg['repository'],'--name',reg['name'],
         '--labels',reg['label'],'--ephemeral','--disableupdate','--work','_work']
    result=subprocess.run(cmd,cwd=folder,env=env,capture_output=True,text=True,timeout=120)
    # Configuration output is kept private; never echo token-bearing diagnostics.
    if result.returncode: raise RuntimeError('Runner configuration failed')
    folders.append((reg,folder))
(root/'registration.json').unlink()
summary=[]
for reg,folder in folders:
    start=time.monotonic()
    print('Starting ephemeral runner: '+reg['repository'],flush=True)
    r=subprocess.run(['runuser','-u','proofci','--','./run.sh'],cwd=folder,timeout=6600)
    summary.append({'repository':reg['repository'],'exit_code':r.returncode,'seconds':round(time.monotonic()-start,2)})
    (root/'ci-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    if r.returncode: raise RuntimeError('Runner exited unsuccessfully')
    # A new runner and fresh mathlib checkout are used for the next repository.
    shutil.rmtree(folder)
print('Ephemeral runner session finished; public workflow conclusions determine proof success.',flush=True)
