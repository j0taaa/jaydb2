import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import child from 'node:child_process';
import {syncBuiltinESMExports} from 'node:module';
import {fixture,repo} from './helpers.mjs';
import {admitSubmission,emitC} from '../../tools/admission/index.mjs';
import {loadToolchain} from '../../tools/admission/bootstrap.mjs';
import {checkBook} from '../../tools/verifier/check.mjs';

const cases=path.join(repo,'tests/admission/cases/v6');
const literal=name=>fs.readFileSync(path.join(cases,name+'.bend'),'utf8');
for(const name of ['intern_self_minimal','intern_self_proof','conversion_nested','intern_self_preseed_control',
 'ordinary_reflexive_boundary','ordinary_boundary_nonrecursive','ordinary_cases_equation','ordinary_domain_boundary',
 'ordinary_boundary_closed_control','ordinary_boundary_lambda_control','quantity_equation','quantity_prefix',
 'dependent_eta','dependent_local_let','vacuous_open']){
 test('API conserva fonte oficial e alvo original: '+name,async t=>{
  const official=child.spawnSync(path.join(repo,'.tools/bend-2.0.39/bin/bend'),[path.join(cases,name+'.bend'),'--check-only'],{encoding:'utf8',timeout:30000});
  assert.equal(official.status,0,official.stdout+official.stderr);
  const f=fixture(t);f.write('Client.bend',f.read('Client.bend')+'\n'+literal(name).replace(/^import Base\s*\n/,''));f.bindCode();
  const admitted=await admitSubmission({...f.manifest(),verification:{deadlineNs:(process.hrtime.bigint()+90000000000n).toString()}});
  assert.equal(admitted.report.primary,true);assert.equal(admitted.report.bendtt,true);
  const names=Object.keys(admitted.book.tlds),first=emitC(admitted);
  assert.equal(emitC(admitted),first);assert.deepEqual(Object.keys(admitted.book.tlds),names);
  if(name==='ordinary_reflexive_boundary'){
   const bridge=admitted.report.verifier.correspondence;
   assert.equal(bridge.route,'structural');assert.ok(bridge.originalTargets.includes('Client:main'));
   assert.ok(bridge.originalTargets.includes('Client:reflexive'));assert.equal(bridge.sameCheckedBook,true);
  }
 });
}

function withR5(t){
 const f=fixture(t),code=literal('ordinary_reflexive_boundary').replace(/^import Base\s*\n/,'').replace('def main(', 'def theorem(');
 f.write('Client.bend',f.read('Client.bend')+'\n'+code);f.bindCode();
 const motive='R.SegurancaPercurso(S.executar(n, Client.programa(), S.esquema(I.config()), s, I.contexto(), I.argumentos()), I.config(), s, I.contexto(), B.codigo(), I.argumentos())';
 f.write('ClientProof.bend',f.read('ClientProof.bend').replace('import ./Bindings.bend as B','import ./Bindings.bend as B\nimport ./Client.bend as Client').replace(/^( {6}| {10})L\.Ambos/gm,(_,indent)=>indent+'%Client.theorem(n): '+motive+';\n'+indent+'L.Ambos'));
 return f;
}

test('certificado usa helper R5 real: alvo exato, guard vivo e C do mesmo Book',async t=>{
 const f=withR5(t),tc=await loadToolchain(),spawn=child.spawnSync,payloads=[];
 child.spawnSync=function(bin,args,options){if(bin===tc.info.verifier.kernelPath)payloads.push(fs.readFileSync(args[0],'utf8'));return spawn(bin,args,options);};syncBuiltinESMExports();
 let admitted;
 try{admitted=await admitSubmission({...f.manifest(),verification:{deadlineNs:(process.hrtime.bigint()+90000000000n).toString()}});}finally{child.spawnSync=spawn;syncBuiltinESMExports();}
 assert.ok(payloads.length);const payload=payloads.at(-1),bridge=admitted.report.verifier.correspondence;
 assert.equal(bridge.route,'structural');assert.ok(bridge.originalTargets.includes('Client:theorem'));
 assert.match(payload,/Evidence\.Client\.theorem\.original_target/);assert.match(payload,/Evidence\.Client\.theorem\.evidence_source_link/);
 assert.ok(admitted.report.instanceClosure.sourceLinks.includes('Bindings:certificado'));
 // This physical dependency is actually in Bindings.certificado's helper
 // closure. Equal reflexive propositions do not excuse its source link.
 const physical=admitted.report.verifier.instances.find(k=>k.startsWith('Client:f~'));
 assert.ok(physical);const def=admitted.book.tlds[physical],saved=def.e;
 const changed=tc.B.term_lower(tc.B.Ann(tc.B.Lam('n',0,()=>tc.B.Lit('Nat',2)),def.T));def.e=changed;
 const bad=checkBook(tc.S,admitted.book,tc.info.verifier);
 assert.match(bad.why,/source_link/);assert.equal(def.e,changed);
 def.e=saved;
 const c=emitC(admitted),names=Object.keys(admitted.book.tlds),file=path.join(f.root,'real.c'),binary=path.join(f.root,'real');
 fs.writeFileSync(file,c);const built=spawn('/usr/bin/clang-19',['-O1','-w',file,'-o',binary,'-lm','-pthread'],{encoding:'utf8',timeout:60000});assert.equal(built.status,0,built.stderr);
 const ran=spawn(binary,[],{encoding:'utf8',timeout:10000});assert.equal(ran.status,0,ran.stderr);assert.equal(ran.stdout.trim(),'Dados.VInt{0, 6}');
 assert.deepEqual(Object.keys(admitted.book.tlds),names);assert.equal(emitC(admitted),c);
 const input=path.join(f.root,'real.bendtt');fs.writeFileSync(input,payload);
 const original=spawn(tc.info.kernelPath,[input],{encoding:'utf8',timeout:60000});assert.equal(original.status,0,original.stdout+original.stderr);assert.equal(original.stdout.trim(),'ALL PROOFS CHECK');
 // A wrong supplied proof remains a primary refusal, never a discovered
 // alternative witness or a payload with the original target omitted.
 f.write('Client.bend',f.read('Client.bend').replace('{f(3n, n) == f(3n, n) : Nat}', '{f(3n, n) == 2n : Nat}'));f.bindCode();
 await assert.rejects(admitSubmission({...f.manifest(),verification:{deadlineNs:(process.hrtime.bigint()+90000000000n).toString()}}),e=>e.code==='PRIMARY_CHECK');
});
