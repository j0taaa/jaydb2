"""Create an isolated gate/cache for staged accounted-emitter tests only.

Never edits shared tools/admission, installed cache, verifier or .tools.
"""
from pathlib import Path
import shutil
import subprocess
ROOT=Path(__file__).resolve().parents[2]

def prepare(target):
    target=Path(target).resolve()
    target.mkdir(parents=True,exist_ok=True)
    for name in ['admission','verifier']:
        shutil.copytree(ROOT/'tools'/name,target/'tools'/name,dirs_exist_ok=True)
    (target/'tools/native').mkdir(parents=True,exist_ok=True)
    if not (target/'.tools').exists():(target/'.tools').symlink_to(ROOT/'.tools',target_is_directory=True)
    subprocess.run(['node','--input-type=module','-',str(ROOT),str(target)],input='''
import {pathToFileURL} from 'node:url';
const [root,target]=process.argv.slice(2);
const {stageAccountedAdapter}=await import(pathToFileURL(root+'/tools/native/accounted_emitter.mjs'));
console.log(JSON.stringify(stageAccountedAdapter(root+'/tools/native/generic.mjs',target+'/tools/native/generic.mjs',root)));
''',text=True,check=True,capture_output=True)
    result=subprocess.run(['node','--input-type=module','-',str(ROOT),str(target)],input="""
import fs from 'node:fs';import {pathToFileURL} from 'node:url';
const [root,target]=process.argv.slice(2);
const {buildFrontend}=await import(pathToFileURL(target+'/tools/admission/build-frontend.mjs'));
const lock=JSON.parse(fs.readFileSync(target+'/tools/admission/toolchain.lock.json'));
const manifest=await buildFrontend(root+'/.tools/bend-source-'+lock.version);
fs.writeFileSync(target+'/tools/admission/frontend.lock.json',JSON.stringify(manifest,null,2)+'\\n');
""",capture_output=True,text=True)
    if result.returncode:raise RuntimeError(result.stderr[-6000:])
    return target

if __name__=='__main__':
    import sys
    print(prepare(sys.argv[1]))
