import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import child from 'node:child_process';
import { compileSubmission, admitSubmission, emitC } from '../../tools/admission/index.mjs';
import { loadToolchain } from '../../tools/admission/bootstrap.mjs';
import { fixture } from './helpers.mjs';

// Inject a kernel verdict in the process boundary, leaving source parsing,
// primary checking, official Safe translation and C emission unchanged.
async function kernelFault(t, why) {
  const { info } = await loadToolchain(), spawn = child.spawn;
  child.spawn = (bin, args, options) => bin === info.kernelPath
    ? spawn(process.execPath, ['-e', `setTimeout(() => { console.log(${JSON.stringify('SOME PROOFS FAIL\n' + why)}); process.exit(1); }, 30);`], options)
    : spawn(bin, args, options);
  t.after(() => { child.spawn = spawn; });
}

function buildC(f, c) {
  const source = path.join(f.root, 'worker.c'), binary = path.join(f.root, 'worker');
  fs.writeFileSync(source, c);
  const built = child.spawnSync('/usr/bin/clang-19', ['-O0', '-w', source, '-o', binary, '-lm', '-pthread'], { encoding: 'utf8' });
  assert.equal(built.status, 0, built.stderr);
  fs.writeFileSync(path.join(f.root, 'compiled'), 'yes');
  // An execution has an observable side effect, even when stdout is ignored.
  const launcher = path.join(f.root, 'launch');
  fs.writeFileSync(launcher, '#!/bin/sh\nprintf executed > "' + path.join(f.root, 'executed') + '"\nexec "' + binary + '"\n', { mode: 0o700 });
  return launcher;
}

test('speculative compilation returns the exact checked C only after both checkers accept', async t => {
  const f = fixture(t);
  let emitted;
  const result = await compileSubmission(f.manifest(), c => { emitted = c; return buildC(f, c); });
  assert.equal(result.admitted.report.primary, true);
  assert.equal(result.admitted.report.bendtt, true);
  assert.equal(emitC(result.admitted), emitted);
  assert.equal(fs.existsSync(path.join(f.root, 'executed')), false);
  const run = child.spawnSync(result.artifact, [], { encoding: 'utf8' });
  assert.equal(run.status, 0, run.stderr);
  assert.equal(run.stdout.trim(), 'Data.VInt{0, 6}');
  assert.equal(fs.readFileSync(path.join(f.root, 'executed'), 'utf8'), 'executed');
});

test('primary rejection never starts speculative compilation', async t => {
  const f = fixture(t);
  f.write('Main.bend', f.read('Main.bend') + '\ndef bad() -> {0 == 1 : U32}: {==}\n');
  let started = false;
  await assert.rejects(compileSubmission(f.manifest(), () => { started = true; }), e => e.code === 'PRIMARY_CHECK');
  assert.equal(started, false);
});

test('a failing concurrent kernel cannot release or execute a compiled worker', async t => {
  await kernelFault(t, 'In injected:\nexpected: <ok>\nobserved: .wrong');
  const f = fixture(t);
  await assert.rejects((async () => {
    const result = await compileSubmission(f.manifest(), c => buildC(f, c));
    child.spawnSync(result.artifact); // Same release-then-launch ordering as the service.
  })(), e => e.code === 'BENDTT_INFRASTRUCTURE');
  assert.equal(fs.readFileSync(path.join(f.root, 'compiled'), 'utf8'), 'yes');
  assert.equal(fs.existsSync(path.join(f.root, 'executed')), false);
});

test('kernel failure wins over simultaneous native build failure', async t => {
  await kernelFault(t, 'out of fuel');
  const f = fixture(t);
  await assert.rejects(compileSubmission(f.manifest(), () => { throw new Error('clang failed'); }),
    e => e.code === 'BENDTT_INFRASTRUCTURE' && /out of fuel/.test(e.message));
});

test('native build failure cannot produce an admitted artifact', async t => {
  const f = fixture(t);
  await assert.rejects(compileSubmission(f.manifest(), () => { throw new Error('clang failed'); }),
    e => e.code === 'COMPILE' && /clang failed/.test(e.message));
});

function changeLiteral(definitions) {
  const pending = [definitions['Client:program'].e], seen = new Set();
  while (pending.length) {
    const term = pending.pop();
    if (!term || typeof term !== 'object' || seen.has(term)) continue;
    seen.add(term);
    if (term.$ === 'Lit' && term.k === 'U32' && term.v === 3) { term.v = 4; return; }
    for (const [key, value] of Object.entries(term)) if (key !== 's') pending.push(value);
  }
  assert.fail('executable literal was not found');
}

for (const when of ['during compilation', 'after admission']) test('Book edits are rejected ' + when, async t => {
  const f = fixture(t), entries = Object.entries;
  let definitions;
  Object.entries = function (value) {
    if (!definitions && value?.['Client:program']?.e) definitions = value;
    return entries(value);
  };
  t.after(() => { Object.entries = entries; });
  if (when === 'during compilation') {
    await assert.rejects(compileSubmission(f.manifest(), () => { changeLiteral(definitions); }),
      e => e.code === 'BENDTT_INFRASTRUCTURE' && /changed a checked definition/.test(e.message));
  } else {
    const admitted = await admitSubmission(f.manifest());
    changeLiteral(definitions);
    assert.throws(() => emitC(admitted), e => e.code === 'COMPILE' && /Book changed after checking/.test(e.message));
  }
});

// Exercise the real host/staging/compiler release boundary, including cleanup.
// The accepted control uses a test compiler sentinel that exits unsuccessfully;
// both calls return failure, but only the accepted Book may launch the sentinel.
test('service discards rejected speculative artifacts before any native execution', t => {
  const f = fixture(t), hook = path.resolve('tests/admission/speculative-fault.mjs');
  for (const verdict of ['reject', 'accept']) {
    const compiled = path.join(f.root, verdict + '-compiled'), executed = path.join(f.root, verdict + '-executed');
    const script = `
from tests.service.test_end_to_end import ROOT, Server
folder = ROOT/'examples/access'
s = Server(folder)
try:
    code,proof = ((folder/name).read_text() for name in ('Client.bend','ClientProof.bend'))
    assert s.call(code,proof,'alice-token','never-publish') == {'status':'failure','value':None}, s.diagnostics()
    assert s.call('', '', 'invalid') == {'status':'authentication','value':None}, s.diagnostics()
    s.finish()
finally:
    s.close()
`;
    const run = child.spawnSync('python3', ['-B', '-c', script], { encoding: 'utf8', timeout: 240000,
      env: { ...process.env, NODE_OPTIONS: '--import ' + hook, JAYDB_TEST_KERNEL: verdict,
        JAYDB_TEST_COMPILED: compiled, JAYDB_TEST_EXECUTED: executed } });
    assert.equal(run.status, 0, run.stdout + run.stderr);
    assert.ok(fs.existsSync(compiled), 'the real Clang compilation completed');
    assert.equal(fs.existsSync(executed), verdict === 'accept', verdict);
    assert.equal(fs.existsSync(compiled + '.premature'), false, 'no receipt before admission');
    const binary = fs.readFileSync(compiled, 'utf8');
    assert.equal(fs.existsSync(binary), false, 'host cleaned the request artifact');
    assert.equal(fs.existsSync(binary + '.json'), false, 'host cleaned the native receipt');
  }
});

// Removing the pre-emission seal would let C consume a different tree than
// the already-fixed kernel payload. Exercise that barrier independently of
// the post-emitter seal and require the builder to remain untouched.
test('Book edit before speculative emission cannot reach the builder', async t => {
  const f = fixture(t), { info } = await loadToolchain();
  const entries = Object.entries, spawn = child.spawn;
  let definitions, changed = false, built = false;
  Object.entries = function (value) {
    if (!definitions && value?.['Client:program']?.e) definitions = value;
    return entries(value);
  };
  child.spawn = function (bin, args, options) {
    if (bin === info.kernelPath) {
      assert.ok(definitions);
      changeLiteral(definitions); changed = true;
    }
    return spawn(bin, args, options);
  };
  t.after(() => { Object.entries = entries; child.spawn = spawn; });
  await assert.rejects(compileSubmission(f.manifest(), () => { built = true; }),
    e => e.code === 'BENDTT_INFRASTRUCTURE' && /changed a checked definition/.test(e.message));
  assert.equal(changed, true);
  assert.equal(built, false);
});


// JavaScript permits throwing falsy primitives. A failed build must remain a
// failure after the checker is reaped, regardless of the thrown value's shape.
test('every thrown builder value rejects admission', async t => {
  for (const cause of [undefined, null, false, 0, '']) {
    const f = fixture(t);
    await assert.rejects(compileSubmission(f.manifest(), () => { throw cause; }),
      e => e.code === 'COMPILE');
  }
});
