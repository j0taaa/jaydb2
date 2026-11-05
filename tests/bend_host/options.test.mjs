import test from 'node:test';
import assert from 'node:assert/strict';
import {options} from '../../host/launch.mjs';
const base=['--configuration','examples/access/Configuration.bend','--seed','examples/access/Seed.bend'];
test('CPU options retain canonical range, ordinary defaults and option failures',()=> {
  assert.ok(options(base).threads>=1&&options(base).threads<=128);
  for(const n of ['1','8','128'])assert.equal(options([...base,'--threads',n]).threads,Number(n));
  for(const n of ['', '0','129','-1','+2','1.5',' 2','many','18446744073709551616'])
    assert.throws(()=>options(['--threads',n]),/--threads/);
  assert.throws(()=>options(['--threads']),/option value/);
  assert.throws(()=>options(['--unknown','x']),/unknown option/);
});
