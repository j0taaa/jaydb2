import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import child from 'node:child_process';
import {pathToFileURL} from 'node:url';
import {fixture,repo} from './helpers.mjs';
import {loadToolchain} from '../../tools/admission/bootstrap.mjs';
import {bookFingerprint} from '../../tools/admission/book-graph.mjs';
import {checkBook,checkKernelFile} from '../../tools/verifier/check.mjs';
import {structuralEmitter} from '../../tools/admission/structural-emitter.mjs';

function primary(B,S,source){
 const book=B.book_nil();B.parse_book(book,B.BEND_DIR+'/',fs.readFileSync(B.BASE_BEND,'utf8'),'',Object.create(null));for(const d of Object.values(book.tlds))d.b=true;
 B.parse_book(book,'/tmp/',source.replace(/^import Base\s*\n/,''),'',Object.create(null));B.book_valid(book);
 for(;;){S.admission_prepare_book(book);const before=bookFingerprint(B,book);B.book_valid(book);S.admission_prepare_book(book);if(bookFingerprint(B,book)===before)return book;}
}
const r5=fs.readFileSync(new URL('./cases/v6/ordinary_reflexive_boundary.bend',import.meta.url),'utf8').replace(/^import Base\s*\n/,'').replace('def main(', 'def witness(');
const source=`def inner(~p: Nat) -> Nat:\n  p\ndef outer(~p: Nat) -> Nat:\n  inner(p)\n`+r5+`\ndef main() -> Nat:\n  outer(1n)\nlaw correct:\n  {main()==1n:Nat}\ndef correct():\n  {==}\n`;

test('ambos kernels preservam vínculos físicos, dependências, aliases e Base',async t=>{
 const {B,S,info}=await loadToolchain(),f=fixture(t);
 for(const mutation of ['control','inner','outer','alias','base','identity-base']){
  const identity=mutation==='identity-base';
  let code=identity?r5+'\ndef main() -> Nat:\n  Nat.add(1n,0n)\n':mutation==='base'?source.replace('  p\ndef outer','  Nat.add(p,0n)\ndef outer'):source;
  const book=primary(B,S,code);let selected;
  if(['inner','alias'].includes(mutation))selected=Object.keys(book.tlds).find(k=>k.startsWith('inner~'));
  if(mutation==='outer')selected=Object.keys(book.tlds).find(k=>k.startsWith('outer~'));
  if(mutation==='base'||identity)selected='Nat.add';
  if(mutation==='alias'){
   const original=selected,alias=selected+'Alias',key=[...book.tmps.inner].find(([,v])=>v===original)[0],xs=key.split('\n');
   xs[0]=JSON.stringify({$:'Ann',x:JSON.parse(xs[0]),T:{$:'Ref',k:'Nat'}});book.tmps.inner.set(xs.join('\n'),alias);book.tlds[alias]={...book.tlds[original]};
   const rewrite=x=>!x||typeof x!=='object'?x:Array.isArray(x)?x.map(rewrite):x.$==='Ref'&&x.k===original?{...x,k:alias}:Object.fromEntries(Object.entries(x).map(([k,v])=>[k,k==='s'?v:rewrite(v)]));
   for(const[k,d]of Object.entries(book.tlds))if(k!==original&&d.$==='Def'&&d.e!==undefined)d.e=rewrite(d.e);selected=alias;
  }
  let changed;
  if(selected){
   const d=book.tlds[selected];let T=d.T,b=B.Lit('Nat',2),binders=[];
   for(let i=0;i<d.n;i++){const F=B.term_wnf(book,T),v=B.Var(F.k,2000000+i);binders.push([F.k,2000000+i]);T=F.B(v);}
   for(const[k,l]of binders.reverse()){const body=b;b=B.Lam(k,l,()=>body);}changed=B.term_lower(B.Ann(b,d.T));d.e=changed;
  }
  const file=path.join(f.root,mutation+'.bendtt'),before=bookFingerprint(B,book);
  const wrapped={...S,admission_safe_emit(book,out,options){const got=S.admission_safe_emit(book,out,options);fs.copyFileSync(out,file);return got;}};
  const got=checkBook(wrapped,book,info.verifier,{initialFuel:'1'}),original=child.spawnSync(info.kernelPath,[file],{encoding:'utf8',timeout:60000});
  assert.equal(got.why===null,mutation==='control',JSON.stringify({mutation,why:got.why}));
  assert.equal(original.status,mutation==='control'?0:1,original.stdout+original.stderr);
  assert.equal(bookFingerprint(B,book),before);
  if(selected)assert.equal(book.tlds[selected].e,changed,'an independent source claim must not overwrite the physical body');
  if(identity){assert.equal(got.correspondence.route,'structural');assert.deepEqual(got.correspondence.identityRoots,['main']);assert.match(got.why,/Nat\.add\.source_link/);}
  if(mutation==='control'){assert.deepEqual(got.correspondence.identityRoots,[],'a changed dependency prevents the identity cut even though main keeps its name');assert.ok(got.correspondence.originalTargets.includes('witness'));}
  if(mutation!=='control')assert.doesNotMatch(got.why,/parse error|out of fuel/i);
 }
});

test('representação Token recursiva exige backlink exato e uma avaliação viva',async t=>{
 const {B,S,info}=await loadToolchain(),f=fixture(t),extended=await import(pathToFileURL(info.sourceDir+'/bend2/safe.ts').href+'?admission-route=structural');
 const book=primary(B,S,fs.readFileSync(path.join(repo,'tests/admission/cases/v6/token-proof-cases.bend'),'utf8')),before=bookFingerprint(B,book);
 const emitter=structuralEmitter(B,extended,{proofRoots:['main'],executionRoots:['main']});let payload;
 const wrapped={...emitter,admission_safe_emit(book,out,options){const got=emitter.admission_safe_emit(book,out,options);payload=fs.readFileSync(out,'utf8');return got;}};
 assert.equal(checkBook(wrapped,book,info.verifier,{initialFuel:'1'}).why,null);
 assert.equal(bookFingerprint(B,book),before);assert.match(payload,/\.Evidence\.innerProof\.original_target/);
 for(const mutation of ['positive','backlink','physical-proof','duplicate-token']){
  let output=payload;
  if(mutation!=='positive'){
   const blocks=output.split('\n\n'),at=blocks.findIndex(x=>/\.Evidence\.main\.evidence_bundle :/.test(x));assert.ok(at>=0);
   const section=blocks[at],split=section.indexOf('=\n  '),header=section.slice(0,split+4);let body=section.slice(split+4),changed=false;
   if(mutation==='duplicate-token')body=body.replace(/\(AdmissionRepresentation[0-9]*\.Input\.Token\.reflect_input r\d+\)/g,call=>{changed=true;return '(!r900000000 = '+call+'; '+call+')';});
   else body=body.replace(/\(\+r(\d+), r(\d+)\)/,(_,value,link)=>{changed=true;return mutation==='backlink'?'(+r'+value+', {==})':'(+r'+(Number(value)-2)+', r'+link+')';});
   assert.ok(changed);blocks[at]=header+body;output=blocks.join('\n\n');
  }
  const file=path.join(f.root,mutation+'.bendtt');fs.writeFileSync(file,output);
  const got=checkKernelFile(file,info.verifier,{initialFuel:'1'}),original=child.spawnSync(info.kernelPath,[file],{encoding:'utf8',timeout:60000});
  assert.equal(got.why===null,mutation==='positive',JSON.stringify({mutation,why:got.why}));assert.equal(original.status,mutation==='positive'?0:1,original.stdout+original.stderr);
  if(mutation!=='positive')assert.doesNotMatch(got.why,/parse error|out of fuel/i);
  if(mutation==='duplicate-token')assert.match(got.why,/affine live code/);
 }
});
