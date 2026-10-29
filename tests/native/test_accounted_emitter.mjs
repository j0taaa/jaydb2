// Staging does not bless a changed Codec merely by recomputing its hash.
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import assert from 'node:assert/strict';
import {fileURLToPath} from 'node:url';
import {stageAccountedAdapter} from '../../tools/native/accounted_emitter.mjs';
const root=path.resolve(path.dirname(fileURLToPath(import.meta.url)),'../..');
const temp=fs.mkdtempSync(path.join(os.tmpdir(),'jaydb-accounted-pins-'));
try {
  const staged=stageAccountedAdapter(root+'/tools/native/generic.mjs',temp+'/next.mjs',root);
  assert.equal(staged.genericSha256,'4b71ed5150db96dd46a87ceeaf91819ba0e42b571818f98698eddc6319037ac3');
  assert.equal(fs.readFileSync(temp+'/next.mjs','utf8'),fs.readFileSync(root+'/tools/native/accounted_generic.next.mjs','utf8'));
  fs.mkdirSync(temp+'/src');fs.mkdirSync(temp+'/contrato');
  for(const file of ['src/Codec.bend','contrato/Dados.bend','contrato/Bytes.bend'])
    fs.copyFileSync(root+'/'+file,temp+'/'+file);
  fs.appendFileSync(temp+'/src/Codec.bend','\n# Different trusted source is not this lowering.\n');
  assert.throws(()=>stageAccountedAdapter(root+'/tools/native/generic.mjs',temp+'/bad.mjs',temp),
    /ACCOUNTED_SOURCE_CHANGED: codec/);
  assert.equal(fs.existsSync(temp+'/bad.mjs'),false);
  console.log(JSON.stringify({stagingStable:true,changedCodecRefused:true,stagedSha256:staged.stagedSha256}));
} finally {fs.rmSync(temp,{recursive:true,force:true});}
