import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import {capture,packet,split,seal,validateSeal,validateProgram,limitsBytes} from '../../host/os.mjs';
const local=path.resolve('target/bend-host/tests');fs.mkdirSync(local,{recursive:true});
test('binary capture drains input/stdout/stderr and waits for reaping',async()=> {
  const input=Buffer.from(Array.from({length:262144},(_,i)=>i%256));
  const r=await capture('/bin/sh',['-c','cat; head -c 131072 /dev/zero >&2'],input);
  assert.equal(r.code,0);assert.deepEqual(r.stdout,input);assert.equal(r.stderr.length,131072);
  const rejected=await capture('/bin/sh',['-c','echo $$; exit 4'],input);
  assert.equal(rejected.code,4);assert.equal(fs.existsSync('/proc/'+rejected.stdout.toString().trim()),false);
  await assert.rejects(capture('/absent-bend-host-worker',[],input));
});
test('all octets and u64 limit boundaries remain exact',()=> {
  const a=Buffer.from(Array.from({length:256},(_,i)=>i)),b=Buffer.from([255,0]);
  assert.deepEqual(split(packet(a,b)),[a,b]);assert.throws(()=>split(Buffer.alloc(7)));
  const limits=limitsBytes({limits:{message:'18446744073709551615',state:'0',response:'4294967296'}});
  assert.equal(limits.readBigUInt64BE(),0xffffffffffffffffn);assert.equal(limits.readBigUInt64BE(16),0x100000000n);
  assert.throws(()=>limitsBytes({limits:{message:'18446744073709551616',state:0,response:0}}));
});
test('sealed artifacts reject substitution and symlinks',()=> {
  const dir=fs.mkdtempSync(path.join(local,'seal-')),file=path.join(dir,'file');
  try {
    fs.writeFileSync(file,Buffer.from([0,255]));const sealed=seal(dir);validateSeal(sealed);
    fs.writeFileSync(file,'changed');assert.throws(()=>validateSeal(sealed));
    fs.unlinkSync(file);fs.symlinkSync('/dev/null',file);assert.throws(()=>validateSeal(sealed));assert.throws(()=>seal(dir));
    assert.throws(()=>validateProgram({path:file,hash:'wrong'}));
  } finally {fs.rmSync(dir,{recursive:true,force:true});}
});
