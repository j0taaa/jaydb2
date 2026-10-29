import assert from 'node:assert/strict';
import fs from 'node:fs';
import { planFields, requirePublishableFieldPlan } from '../../tools/native/field_plan.mjs';
const file=process.argv[2] ?? 'tests/native/evidence/field-codec.c.constructors.json';
const metadata=JSON.parse(fs.readFileSync(file,'utf8'));
const plan=planFields(metadata);
assert.equal(plan.runtimeCoverageComplete,false);
for(const ctor of ['VTexto','VListaVazia','VRegistroVazio','VInt','VBool','VAusente'])
  assert(plan.sites.some(s=>s.constructor==='Dados:'+ctor),ctor);
assert(plan.sites.some(s=>s.classification==='partial-text'));
assert(plan.sites.some(s=>s.classification==='partial-sequence-candidate'));
assert(plan.sites.some(s=>s.storage==='inline-or-flattened'));
assert(plan.sites.some(s=>s.storage==='arena'));
const original=plan.guards.find(s=>s.origin==='Codec:concluir_palavra');
assert.deepEqual(original.arguments.map(a=>a.name),['f','alto','baixo','pilha','corpo','teto']);
const open=plan.guards.find(s=>s.origin==='Codec:abrir_conferido');
assert.deepEqual(open.arguments.find(a=>a.name==='n').layout,['w32','w32']);
assert.deepEqual(open.arguments.find(a=>a.name==='c').arms,['Codec:Cabe','Codec:Curto','Codec:Grande']);
for(const candidate of [plan,{...plan,runtimeCoverageComplete:true,pending:[]}])
  assert.throws(()=>requirePublishableFieldPlan(candidate),/FIELD_COVERAGE_INCOMPLETE/);
const without=structuredClone(metadata);
without.sites=without.sites.filter(s=>!(s.kind==='decoder-guard-entry' && s.origin==='Codec:abrir_conferido'));
assert.throws(()=>planFields(without),/missing effective decoder guard/);
const renamed=structuredClone(metadata);
renamed.sites.find(s=>s.kind==='decoder-guard-entry' && s.origin==='Codec:concluir_palavra')
  .arguments.find(a=>a.name==='baixo').name='storage_bytes';
assert.throws(()=>planFields(renamed),/changed trusted guard parameters/);
fs.writeFileSync('tests/native/evidence/field-plan.json',JSON.stringify(plan,null,2)+'\n');
console.log(JSON.stringify({guards:plan.guards.length,fieldSites:plan.sites.length,
  actualNativeStoresInstrumented:false,publicationRefused:true,
  unchangedC:metadata.emittedCUnchanged,primary:metadata.primary,bendtt:metadata.bendtt}));
