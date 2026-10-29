import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import child from 'node:child_process';
import { repo } from './helpers.mjs';
import { sha256 } from '../../tools/admission/bootstrap.mjs';

const launcher = path.join(repo, 'tools/admission/run.py');
const probe = path.join(repo, 'tests/admission/resource_probe.mjs');
const run = scenario => child.spawnSync('/usr/bin/python3', ['-B', launcher, '--memory-bytes', '536870912', '--', process.execPath, probe, scenario], {
  encoding: 'utf8', timeout: 30000,
});

for (const scenario of ['deep', 'template-depth', 'template-width', 'low-fuel']) {
  test(`recursos gerais, ambos checkers reais: ${scenario}`, () => {
    const got = run(scenario);
    assert.equal(got.status, 0, got.stderr + got.stdout);
    const result = JSON.parse(got.stdout);
    assert.equal(result.primary, true);
    assert.equal(result.bendtt, true);
    assert.equal(result.frontendResourcesSha256, sha256(fs.readFileSync(path.join(repo, 'tools/admission/frontend-resources.mjs'))));
    if (scenario === 'low-fuel') assert.ok(BigInt(result.attempts) > 1n);
    if (scenario === 'template-depth') assert.match(result.baseline, /64 levels at most/);
    if (scenario === 'template-width') assert.match(result.baseline, /a ~ argument that stops growing/);
  });
}

test('frontend com stack crescente conserva a recusa matemática', () => {
  const got = run('deep-false');
  assert.equal(got.status, 2, got.stderr + got.stdout);
  assert.match(got.stderr, /"code":"(?:PRIMARY_CHECK|BENDTT_CHECK)"/);
});

test('launcher lê Nat público com mais de 4300 dígitos por arquivo, sem argv/env gigante', t => {
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), 'jaydb-resources-test-'));
  t.after(() => fs.rmSync(directory, { recursive: true, force: true }));
  const resources = path.join(directory, 'resources.json');
  fs.writeFileSync(resources, JSON.stringify({ compiler_memory_bytes: '1' + '0'.repeat(5000) }));
  const got = child.spawnSync('/usr/bin/python3', ['-B', launcher, '--resources-json', resources, '--describe'], { encoding: 'utf8' });
  assert.equal(got.status, 0, got.stderr);
  assert.equal(JSON.parse(got.stdout).stack, 'RLIM_INFINITY + V8 lowest user address 65536');
});

for (const amount of ['4294967296', '1' + '0'.repeat(100)]) {
  test(`orçamento grande não estoura a aritmética da stack V8: ${amount.length} dígitos`, () => {
    const got = child.spawnSync('/usr/bin/python3', ['-B', launcher, '--memory-bytes', amount, '--', process.execPath, '-e', 'console.log("ready")'], { encoding: 'utf8', timeout: 5000 });
    assert.equal(got.status, 0, got.stderr);
    assert.equal(got.stdout.trim(), 'ready');
  });
}
