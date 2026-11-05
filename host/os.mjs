// Trusted byte/OS adapter. No request routing, handle registry or publication.
import fs from 'node:fs';
import path from 'node:path';
import os from 'node:os';
import net from 'node:net';
import {randomBytes} from 'node:crypto';
import {spawn} from 'node:child_process';
import {sha256} from '../tools/admission/bootstrap.mjs';

export const word = n => { const b=Buffer.alloc(8); b.writeBigUInt64BE(BigInt(n)); return b; };
export const packet = (a,b=Buffer.alloc(0)) => Buffer.concat([word(a.length),a,b]);
export function split(b) {
  if(b.length<8 || b.readBigUInt64BE()>BigInt(b.length-8)) throw Object.assign(Error('invalid internal length'),{code:'HOST_TRANSPORT'});
  const n=Number(b.readBigUInt64BE()); return [b.subarray(8,8+n),b.subarray(8+n)];
}
export async function writeAll(stream, bytes) {
  // Writable also emits an error after reporting it to the write callback.
  // Keep that emission observed so the owner can stop dispatch and clean up.
  if(stream.listenerCount('error')===0) stream.on('error',()=>{});
  await new Promise((resolve,reject)=>stream.write(bytes,error=>error?reject(error):resolve()));
}
export class Reader {
  constructor(stream) { this.iterator=stream[Symbol.asyncIterator](); this.pending=Buffer.alloc(0); }
  async read(n) {
    const chunks=[]; let total=0;
    while(total<n) {
      if(!this.pending.length) { const v=await this.iterator.next(); if(v.done) break; this.pending=v.value; }
      const k=Math.min(n-total,this.pending.length); chunks.push(this.pending.subarray(0,k));
      this.pending=this.pending.subarray(k); total+=k;
    }
    return Buffer.concat(chunks,total);
  }
  async frame() {
    const h=await this.read(8); if(!h.length) return null;
    if(h.length!==8) throw Error('truncated adapter frame');
    const n=h.readBigUInt64BE(); if(n>BigInt(Number.MAX_SAFE_INTEGER)) throw Error('unaddressable adapter frame');
    const b=await this.read(Number(n)); if(b.length!==Number(n)) throw Error('truncated adapter body'); return b;
  }
}

// spawn/close (not exit) guarantees stdio has drained as well as waitpid.
// No shell, text decoding, production deadline or output truncation.
export function capture(program,args,input,children=new Set(),extraEnv={}) {
  return new Promise((resolve,reject)=> {
    const child=spawn(program,args,{env:{...process.env,BEND_NO_TELEMETRY:'1',...extraEnv},stdio:['pipe','pipe','pipe']});
    children.add(child); const stdout=[],stderr=[]; let failure,writeFailure;
    child.on('error',e=>{ failure=e; if(child.pid) child.kill('SIGKILL'); });
    child.stdout.on('data',b=>stdout.push(b)); child.stderr.on('data',b=>stderr.push(b));
    child.stdout.on('error',e=>{failure=e;child.kill('SIGKILL');});
    child.stderr.on('error',e=>{failure=e;child.kill('SIGKILL');});
    child.stdin.on('error',e=>{writeFailure=e;}); child.stdin.end(input);
    child.on('close',(code,signal)=> {
      children.delete(child);
      if(failure || (code===0 && writeFailure)) reject(failure??writeFailure);
      else resolve({code,signal,stdout:Buffer.concat(stdout),stderr:Buffer.concat(stderr)});
    });
  });
}
const fail=(code,message)=>{throw Object.assign(Error(message),{code});};
const read=name=>fs.readFileSync(name);
export function loadProgram(file) {
  const manifest=JSON.parse(read(file+'.json'));
  if(manifest.format!=='jaydb-official-c-v1') fail('HOST_NATIVE','invalid official executable manifest');
  const p={path:file,hash:manifest.executableSha256}; validateProgram(p); return p;
}
export function validateProgram(p) {
  if(sha256(read(p.path))!==p.hash) fail('HOST_NATIVE','official executable hash mismatch');
}
export function seal(dir) {
  const files=[];
  for(const entry of fs.readdirSync(dir,{withFileTypes:true})) {
    const p=path.join(dir,entry.name);
    if(entry.isDirectory()) files.push(...seal(p));
    else if(entry.isFile()) files.push([p,sha256(read(p))]);
    else fail('PREPARED_INTEGRITY','nonregular prepared artifact');
  }
  return files;
}
export function validateSeal(files) {
  for(const [p,hash] of files) if(!fs.lstatSync(p).isFile() || sha256(read(p))!==hash)
    fail('PREPARED_INTEGRITY','sealed prepared artifact changed');
}
export const limitsBytes=report=> {
  const limits=report.limits;
  if(!limits || Object.keys(limits).sort().join(',')!=='message,response,state') fail('HOST_JSON','expected three logical limits');
  return Buffer.concat(['message','state','response'].map(k=> {
    if(!/^(0|[1-9][0-9]*)$/.test(String(limits[k])) || BigInt(limits[k])>0xffffffffffffffffn) fail('CONFIGURATION',k+' is outside the uint64 transport domain');
    return word(limits[k]);
  }));
};
export class Adapter {
  constructor(options,controller) { this.options=options; this.controller=controller; this.resources=new Map(); this.children=new Set(); this.sequence=0; this.next=0; }
  async helper(script,args) {
    const result=await capture('node',['--stack_size=65536',script,...args],Buffer.alloc(0),this.children,
      {JAYDB_CONTROLLER_PID:String(this.controller)});
    if(result.code===0) return JSON.parse(result.stdout);
    for(const data of [result.stderr,result.stdout]) for(const line of data.toString('utf8').split('\n').reverse()) {
      let r; try {r=JSON.parse(line);} catch {continue;}
      if(typeof r.code==='string') fail(r.code,r.message??'compilation failed');
    }
    fail('HELPER',result.stderr.toString('utf8'));
  }
  async connectInspector() {
    if(!this.options.inspect) return;
    this.inspector=net.createConnection(this.options.inspect);
    await new Promise((resolve,reject)=>{this.inspector.once('connect',resolve);this.inspector.once('error',reject);});
    this.inspector.on('error',()=>{this.inspector?.destroy();this.inspector=null;});
  }
  async initialize() {
    await this.connectInspector();
    this.directory=fs.mkdtempSync(path.join(this.options.temp,`jaydb2-${process.pid}-`)); fs.chmodSync(this.directory,0o700);
    const o=this.options, report=await this.helper(path.join(o.root,'tools/service/stage.mjs'),
      ['initialize',this.directory,o.configuration,o.seed,o.source,o.kernel]);
    this.stage=report.stagePath;
    for(const [name,p] of Object.entries(report.programs)) this.resources.set(name==='initialize'?'initial':name,{directory:path.dirname(p),program:loadProgram(p)});
    if(this.inspector) this.seed=read(path.join(this.directory,'initialize/Seed.bend')).toString('utf8');
    return limitsBytes(report);
  }
  resource(id) { const r=this.resources.get(id.toString('utf8')); if(!r) fail('HOST_RESOURCE','unknown OS resource'); return r; }
  async run(id,input) {
    const p=this.resource(id).program; validateProgram(p);
    const r=await capture(p.path,['+RTS','--threads',String(this.options.threads),'--gpu','off','-RTS'],input,this.children,
      {BENDRTS:''});
    if(r.code!==0) fail('NATIVE',`worker ${r.signal??r.code}: ${r.stderr.toString('utf8')}`);
    return r.stdout;
  }
  async readInput(bytes) {
    const n=bytes.readBigUInt64BE(); if(n>BigInt(Number.MAX_SAFE_INTEGER)) fail('HOST_TRANSPORT','message length is not representable');
    const chunks=[]; let used=0;
    while(used<Number(n)) {
      const b=Buffer.alloc(Math.min(65536,Number(n)-used));
      const k=await new Promise((resolve,reject)=>fs.read(0,b,0,b.length,null,(e,k)=>e?reject(e):resolve(k)));
      if(!k) break; chunks.push(b.subarray(0,k)); used+=k;
    }
    return Buffer.concat(chunks,used);
  }
  async inspect(bytes) {
    if(!this.inspector) {
      if(bytes[0]===1) {++this.sequence;this.diagnostic=null;}
      return Buffer.alloc(0);
    }
    const event=bytes[0], [payload,state]=split(bytes.subarray(1));
    let metadata;
    if(event===0) {
      const sources={}; for(const e of fs.readdirSync(path.join(this.directory,'public'),{withFileTypes:true}))
        if(e.isFile()) sources[e.name]=read(path.join(this.directory,'public',e.name)).toString('utf8');
      const environment=JSON.parse(read(path.join(this.directory,'environment.json')));
      metadata={event:'initialized',environment,sources,seed:this.seed,limits:this.initLimits};
    } else if(event===1) { ++this.sequence; metadata={event:'completed',diagnostic:this.diagnostic??null}; this.diagnostic=null; }
    else if(event===2) { const [code,a]=split(payload),[proof,b]=split(a),[instance,bindings]=split(b);
      metadata={event:'authenticated',generated_sources:{'Instance.bend':instance.toString('utf8'),'Bindings.bend':bindings.toString('utf8')}};
    } else { const [key,a]=split(payload),[code,proof]=split(a);
      metadata={event:'prepared-resolved',handle:key.toString('utf8'),original_code:code.toString('utf8'),universal_proof:proof.toString('utf8')}; }
    if(!this.inspector) return Buffer.alloc(0);
    metadata.sequence=this.sequence;
    const stream=this.inspector;
    try {
      await new Promise((resolve,reject)=> {
        const timer=setTimeout(()=>{stream.destroy();reject(Error('inspection timeout'));},2000);
        stream.write(Buffer.concat([packet(Buffer.from(JSON.stringify(metadata))),packet(state)]),error=>{clearTimeout(timer);error?reject(error):resolve();});
      });
    } catch(e) { console.error('jaydb2: INSPECTOR: '+e.message);stream.destroy();this.inspector=null; }
    return Buffer.alloc(0);
  }
  async effect(command) {
    const op=command[0], b=command.subarray(1);
    switch(op) {
      case 0: { const limits=await this.initialize(); this.initLimits=Object.fromEntries(['message','state','response'].map((k,i)=>[k,JSON.rawJSON(limits.readBigUInt64BE(i*8).toString())])); return limits; }
      case 1: return this.readInput(b);
      case 2: await writeAll(process.stdout,b); return Buffer.alloc(0);
      case 3: { const id='artifact-'+this.next++, directory=fs.mkdtempSync(path.join(this.directory,'request-'));
        fs.chmodSync(directory,0o700);this.resources.set(id,{directory});return Buffer.from(id); }
      case 4: { const mode=b[0], [id,metadata]=split(b.subarray(1)), resource=this.resource(id);
        const [code,a]=split(metadata),[proof,c]=split(a),[instance,bindings]=split(c), directory=path.join(resource.directory,'metadata');
        fs.mkdirSync(directory,{mode:0o700});
        for(const [name,data] of [['Client.bend',code],['ClientProof.bend',proof],['Instance.bend',instance],['Bindings.bend',bindings]])
          fs.writeFileSync(path.join(directory,name),data,{mode:0o600,flag:'wx'});
        const report=await this.helper(this.stage,[mode===0?'prepare':'execute',this.directory,resource.directory,directory,this.options.source,this.options.kernel]);
        resource.program=loadProgram(report.program);
        return Buffer.concat([limitsBytes(report),Buffer.from(report.certificateMode??'')]); }
      case 5: { const [id,input]=split(b); return this.run(id,input); }
      case 6: { const r=this.resource(b); r.sealed=[...seal(r.directory),...seal(path.join(this.directory,'public')),...seal(path.join(this.directory,'runtime'))];return Buffer.alloc(0); }
      case 7: { const r=this.resource(b); fs.rmSync(r.directory,{recursive:true});this.resources.delete(b.toString('utf8'));return Buffer.alloc(0); }
      case 8: return Buffer.from(randomBytes(32).toString('hex'));
      case 9: return this.inspect(b);
      case 11: validateSeal(this.resource(b).sealed);return Buffer.alloc(0);
      case 12: { const [c,message]=split(b),code=c.toString('utf8');
        if(this.diagnostic?.code!==code) {this.diagnostic={code,message:message.toString('utf8')||code};console.error(`jaydb2: ${code}: ${this.diagnostic.message}`);}
        return Buffer.alloc(0); }
      default: fail('HOST_EFFECT','unknown OS operation');
    }
  }
  async dispatch(command) {
    try {return Buffer.concat([Buffer.from([1]),await this.effect(command)]);}
    catch(e) {
      const code=e.code??'HOST_IO';this.diagnostic={code,message:e.message};
      console.error(`jaydb2: ${code}: ${e.message}`);
      return Buffer.concat([Buffer.from([0]),Buffer.from(code)]);
    }
  }
  async close() {
    const active=[...this.children]; const waited=active.map(c=>new Promise(resolve=>c.once('close',resolve)));
    for(const c of active) c.kill('SIGKILL'); await Promise.all(waited);
    this.inspector?.destroy(); if(this.directory) fs.rmSync(this.directory,{recursive:true,force:true});
  }
}
