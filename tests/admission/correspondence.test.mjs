import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import child from 'node:child_process';
import { syncBuiltinESMExports } from 'node:module';
import { admitSubmission, emitC } from '../../tools/admission/index.mjs';
import { loadToolchain, sha256 } from '../../tools/admission/bootstrap.mjs';
import { checkBook, VerifierInfrastructure } from '../../tools/verifier/check.mjs';
import { fixture } from './helpers.mjs';

function runC(root, source, name) {
  const file = path.join(root, name + '.c'), binary = path.join(root, name);
  fs.writeFileSync(file, source);
  const built = child.spawnSync('/usr/bin/clang-19', ['-O1', '-w', file, '-o', binary, '-lm', '-pthread'],
    { encoding: 'utf8', timeout: 60000 });
  assert.equal(built.status, 0, built.stderr);
  const run = child.spawnSync(binary, [], { encoding: 'utf8', timeout: 10000 });
  assert.equal(run.status, 0, run.stderr);
  return run.stdout.trim();
}

// The official translator and kernel check the same private Book emitted to C.
test('official tools preserve checked source and emitted behavior', async t => {
  const f = fixture(t), { info } = await loadToolchain();
  f.write('Client.bend', f.read('Client.bend') + '\n# exact source: IO @unsafe ?all\n');
  f.bindCode();
  const exactSource = f.read('Client.bend'), spawn = child.spawnSync, payloads = [];
  child.spawnSync = function (bin, args, options) {
    if (bin === info.kernelPath) {
      assert.equal(args.length, 1); // The original CLI has no dynamic fuel argument.
      payloads.push(fs.readFileSync(args[0]));
    }
    return spawn(bin, args, options);
  };
  syncBuiltinESMExports();
  let admitted;
  try { admitted = await admitSubmission(f.manifest()); }
  finally { child.spawnSync = spawn; syncBuiltinESMExports(); }
  assert.equal(admitted.report.primary, true);
  assert.equal(admitted.report.bendtt, true);
  assert.equal(admitted.report.verifier.kernelSha256, info.kernelSha256);
  assert.equal('book' in admitted, false);
  assert.equal(admitted.sources.find(s => s.path === 'Client.bend').text, exactSource);
  assert.equal(payloads.length, 1);
  assert.equal(admitted.report.verifier.inputSha256, sha256(payloads[0]));
  for (const [file, expected] of Object.entries(info.files)) {
    assert.equal(sha256(fs.readFileSync(path.join(info.sourceDir, file))), expected);
  }
  f.write('Client.bend', 'changed after admission');
  const c = emitC(admitted);
  assert.equal(emitC(admitted), c);
  assert.equal(runC(f.root, c, 'checked'), 'Data.VInt{0, 6}');
});

test('in-place changes to a checked runtime tree cannot survive translation', async t => {
  const f = fixture(t), { info } = await loadToolchain();
  const entries = Object.entries, spawn = child.spawnSync;
  let definitions, changed = false, admitted, failure;
  Object.entries = function (value) {
    if (!definitions && value?.['Client:program']?.e) definitions = value;
    return entries(value);
  };
  child.spawnSync = function (bin, args, options) {
    if (bin === info.kernelPath && !changed) {
      assert.ok(definitions, 'capture the actual private checked Book');
      const pending = [definitions['Client:program'].e], seen = new Set();
      while (pending.length && !changed) {
        const term = pending.pop();
        if (!term || typeof term !== 'object' || seen.has(term)) continue;
        seen.add(term);
        if (term.$ === 'Lit' && term.k === 'U32' && term.v === 3) {
          term.v = 4; changed = true;
        } else for (const [key, child] of entries(term)) if (key !== 's') pending.push(child);
      }
      assert.equal(changed, true, 'change the executable literal after the kernel payload is fixed');
    }
    return spawn(bin, args, options);
  };
  syncBuiltinESMExports();
  try { admitted = await admitSubmission(f.manifest()); }
  catch (error) { failure = error; }
  finally { Object.entries = entries; child.spawnSync = spawn; syncBuiltinESMExports(); }
  if (admitted) assert.fail('Accepted altered behavior: ' + runC(f.root, emitC(admitted), 'changed-tree'));
  assert.equal(changed, true);
  assert.equal(failure?.code, 'BENDTT_INFRASTRUCTURE', failure?.message);
  assert.match(failure.message, /changed a checked definition/);
});

// Historical R4 came from the removed interning adapter. The official
// frontend already handles this nested specialization and C must return 1.
test('official nested template preserves the checked result in C', async t => {
  const f = fixture(t), prefix = f.read('Main.bend').split('def result')[0];
  f.write('Main.bend', prefix + 'def intern(~p: Nat) -> Nat:\n  p\ndef main() -> Nat:\n  intern(intern(1n))\n');
  assert.equal(runC(f.root, emitC(await admitSubmission(f.manifest())), 'nested'), '1n');
});

// Historical R5 passes primary checking but the original Safe translator does
// not represent a template applied to a run-time proof variable. Keep both the
// rejection and its ordinary-argument control; no adapter or fallback is used.
test('official dependent-template translation limit is technical', async () => {
  const { B, S, info } = await loadToolchain();
  const source = `def f(~p: Nat, n: Nat) -> Nat:
  match n:
    case Zero{}: p
    case Succ{x}: f(p, x)
def helper(p: Nat, n: Nat) -> {f(p, n) == p : Nat}:
  match n:
    case Zero{}: {==}
    case Succ{x}: helper(p, x)
def main(n: Nat) -> {f(3n, n) == 3n : Nat}:
  helper(3n, n)
`;
  for (const templated of [false, true]) {
    const book = B.book_nil();
    B.parse_book(book, B.BEND_DIR + '/', fs.readFileSync(B.BASE_BEND, 'utf8'), '', Object.create(null));
    for (const definition of Object.values(book.tlds)) definition.b = true;
    B.parse_book(book, '/tmp/', templated ? source : source.replace('~p:', 'p:'), '', Object.create(null));
    B.book_valid(book);
    if (templated) assert.throws(() => checkBook(S, book, info.verifier),
      e => e instanceof VerifierInfrastructure && /template argument that depends on a run-time value/.test(e.message));
    else assert.equal(checkBook(S, book, info.verifier).why, null);
  }
});
