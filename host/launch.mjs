#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import os from 'node:os';
import {fileURLToPath} from 'node:url';
import {spawn} from 'node:child_process';
import {sha256,toolchainLock} from '../tools/admission/bootstrap.mjs';
import {Adapter,Reader,packet,writeAll} from './os.mjs';
const root=path.resolve(path.dirname(fileURLToPath(import.meta.url)),'..');
export function options(args) {
  const o={root,temp:process.env.TMPDIR??path.join(root,'target/tmp'),threads:Math.min(os.availableParallelism(),128),
    source:path.join(root,'.tools/bend-source-'+toolchainLock.version),kernel:path.join(root,'.tools/bendtt-'+toolchainLock.kernelSha256)};
  const names={'--configuration':'configuration','--seed':'seed','--threads':'threads','--bend-source':'source','--bendtt':'kernel','--inspect-socket':'inspect'};
  for(let i=0;i<args.length;++i) {
    if(args[i]==='--help'||args[i]==='-h') { console.log('Usage: jaydb2 --configuration FILE --seed FILE [--threads N] [--bend-source DIR] [--bendtt FILE] [--inspect-socket ADMIN_SOCKET]\n\n--threads N  CPU workers per native program, 1 to 128 (default: available CPU parallelism, capped at 128)'); return null; }
    const name=names[args[i]]; if(!name) throw Error('unknown option '+args[i]);
    if(++i===args.length) throw Error('expected an option value');
    if(name==='threads') {
      if(!/^[0-9]+$/.test(args[i])||BigInt(args[i])<1n||BigInt(args[i])>128n) throw Error('--threads must be an integer from 1 to 128');
      o.threads=Number(args[i]);
    } else o[name]=args[i];
  }
  for(const key of ['configuration','seed']) if(!o[key]) throw Error('--'+key+' is required');
  for(const key of ['configuration','seed','source','kernel']) o[key]=fs.realpathSync(o[key]);
  fs.mkdirSync(o.temp,{recursive:true});return o;
}
async function main() {
  const o=options(process.argv.slice(2));if(!o)return;
  const binary=path.join(root,'target/bend-host/controller'), manifest=JSON.parse(fs.readFileSync(binary+'.json'));
  if(sha256(fs.readFileSync(binary))!==manifest.executableSha256) throw Error('controller hash mismatch; run make build-bend-host');
  const child=spawn(binary,['+RTS','--threads','1','--gpu','off','-RTS'],{stdio:['pipe','pipe','inherit']});
  const adapter=new Adapter(o,child.pid);let ended=false;
  const exit=new Promise(resolve=>child.once('close',(code,signal)=>{ended=true;resolve(code??1);}));
  child.on('error',e=>{console.error(e.message);});child.stdin.on('error',()=>{});
  child.once('exit',()=>{for(const c of adapter.children)c.kill('SIGKILL');});
  // A controller killed while an exact fd0 read is pending must not leave
  // Node's blocking filesystem read keeping the adapter alive. Reap all owned
  // helpers and remove resources first, then terminate even with idle stdin.
  child.once('close',async code=>{
    try {await adapter.close();}
    catch(e) {console.error('jaydb2: CLEANUP: '+e.message);process.exit(1);}
    process.exit(code??1);
  });
  const stop=()=>child.kill('SIGTERM');process.once('SIGTERM',stop);process.once('SIGINT',stop);
  try {
    const reader=new Reader(child.stdout);
    for(;;) {
      const command=await reader.frame();if(command===null)break;
      const result=await adapter.dispatch(command);
      if(ended)break;await writeAll(child.stdin,packet(result));
    }
    process.exitCode=await exit;
  } finally { if(!ended)child.kill('SIGKILL');await exit;await adapter.close(); }
}
if(process.argv[1]&&path.resolve(process.argv[1])===fileURLToPath(import.meta.url))
  main().catch(e=>{console.error('jaydb2: HOST_IO: '+e.message);process.exitCode=1;});
