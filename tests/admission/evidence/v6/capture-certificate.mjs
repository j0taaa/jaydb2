// Reproduce the certificate-closure regression and retain its exact artifacts.
// Optional development harness; no production dispatch or resource policy.
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import child from 'node:child_process';
import {createHash} from 'node:crypto';
import {syncBuiltinESMExports} from 'node:module';
import {fixture,repo} from '../../helpers.mjs';
import {admitSubmission,emitC} from '../../../../tools/admission/index.mjs';
import {loadToolchain} from '../../../../tools/admission/bootstrap.mjs';
import {checkBook} from '../../../../tools/verifier/check.mjs';
import {bookFingerprint} from '../../../../tools/admission/book-graph.mjs';

const destination=path.resolve(process.argv[2]??'/tmp/jaydb2-v6-certificate-evidence');
fs.mkdirSync(destination,{recursive:true});
let cleanup;const f=fixture({after(fn){cleanup=fn;}});
const hash=bytes=>createHash('sha256').update(bytes).digest('hex');
try{
 const literal=fs.readFileSync(path.join(repo,'tests/admission/cases/v6/ordinary_reflexive_boundary.bend'),'utf8');
 f.write('Client.bend',f.read('Client.bend')+'\n'+literal.replace(/^import Base\s*\n/,'').replace('def main(', 'def theorem('));f.bindCode();
 const motive='R.SegurancaPercurso(S.executar(n, Client.programa(), S.esquema(I.config()), s, I.contexto(), I.argumentos()), I.config(), s, I.contexto(), B.codigo(), I.argumentos())';
 f.write('ClientProof.bend',f.read('ClientProof.bend').replace('import ./Bindings.bend as B','import ./Bindings.bend as B\nimport ./Client.bend as Client').replace(/^( {6}| {10})L\.Ambos/gm,(_,indent)=>indent+'%Client.theorem(n): '+motive+';\n'+indent+'L.Ambos'));
 const tc=await loadToolchain(),spawn=child.spawnSync,payloads=[];
 child.spawnSync=function(bin,args,options){if(bin===tc.info.verifier.kernelPath)payloads.push(fs.readFileSync(args[0]));return spawn(bin,args,options);};syncBuiltinESMExports();
 let admitted;
 try{admitted=await admitSubmission(f.manifest());}finally{child.spawnSync=spawn;syncBuiltinESMExports();}
 assert.ok(payloads.length);const payload=payloads.at(-1),bridge=admitted.report.verifier.correspondence;
 assert.equal(bridge.route,'structural');assert.ok(bridge.originalTargets.includes('Client:theorem'));
 assert.match(payload.toString(),/Evidence\.Client\.theorem\.original_target/);
 assert.match(payload.toString(),/Evidence\.Client\.theorem\.evidence_source_link/);
 assert.ok(admitted.report.instanceClosure.sourceLinks.includes('Bindings:certificado'));
 fs.writeFileSync(path.join(destination,'certificate.bendtt'),payload);
 const before=bookFingerprint(tc.B,admitted.book),physical=admitted.report.verifier.instances.find(k=>k.startsWith('Client:f~'));
 assert.ok(physical);const def=admitted.book.tlds[physical],saved=def.e;
 const changed=tc.B.term_lower(tc.B.Ann(tc.B.Lam('n',0,()=>tc.B.Lit('Nat',2)),def.T));def.e=changed;
 const mutatedFingerprint=bookFingerprint(tc.B,admitted.book);
 const wrapped={...tc.S,admission_safe_emit(book,out,options){const got=tc.S.admission_safe_emit(book,out,options);fs.copyFileSync(out,path.join(destination,'mutated-dependency.bendtt'));return got;}};
 const bad=checkBook(wrapped,admitted.book,tc.info.verifier);
 assert.match(bad.why,/source_link/);assert.equal(def.e,changed);assert.equal(bookFingerprint(tc.B,admitted.book),mutatedFingerprint);
 def.e=saved;assert.equal(bookFingerprint(tc.B,admitted.book),before);
 const c=emitC(admitted);fs.writeFileSync(path.join(destination,'certificate.c'),c);assert.equal(emitC(admitted),c);
 const executable=path.join(f.root,'certificate');
 const built=spawn('/usr/bin/clang-19',['-O1','-w',path.join(destination,'certificate.c'),'-o',executable,'-lm','-pthread'],{encoding:'utf8'});assert.equal(built.status,0,built.stderr);
 const ran=spawn(executable,[],{encoding:'utf8'});assert.equal(ran.status,0,ran.stderr);assert.equal(ran.stdout.trim(),'Dados.VInt{0, 6}');
 const originals={};
 for(const name of ['certificate','mutated-dependency']){
  const r=spawn(tc.info.kernelPath,[path.join(destination,name+'.bendtt')],{encoding:'utf8'});
  fs.writeFileSync(path.join(destination,name+'.original.log'),r.stdout+r.stderr);
  assert.equal(r.status,name==='certificate'?0:1,r.stdout+r.stderr);
  originals[name]={status:r.status,stdout:r.stdout,stderr:r.stderr};
 }
 fs.mkdirSync(path.join(destination,'source'),{recursive:true});
 for(const name of f.roles.keys())fs.copyFileSync(path.join(f.root,name),path.join(destination,'source',name));
 fs.writeFileSync(path.join(destination,'submission.json'),JSON.stringify(f.manifest(),null,2)+'\n');
 const files=Object.fromEntries(fs.readdirSync(destination).filter(name=>fs.statSync(path.join(destination,name)).isFile()).map(name=>[name,hash(fs.readFileSync(path.join(destination,name)))]));
 const result={status:'PASS',scope:'actual Bindings.certificado uses Client.theorem(n) through original J; exact evidence and physical dependency link required',correspondence:bridge,physicalDependency:physical,mutatedDependency:{why:bad.why,originalBodyPreservedByCheck:true},originalKernels:originals,cOutput:ran.stdout.trim(),sameBook:true,noDeclarationAfterKernel:true,files};
 fs.writeFileSync(path.join(destination,'result.json'),JSON.stringify(result,null,2)+'\n');
 console.log(JSON.stringify({status:result.status,physicalDependency:physical,cOutput:result.cOutput,payloadSha256:files['certificate.bendtt'],negative:bad.why}));
}finally{cleanup?.();}
