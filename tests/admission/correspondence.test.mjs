import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import child from 'node:child_process';
import { syncBuiltinESMExports } from 'node:module';
import { admitSubmission, emitC } from '../../tools/admission/index.mjs';
import { loadToolchain } from '../../tools/admission/bootstrap.mjs';
import { checkBook } from '../../tools/verifier/check.mjs';
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

const r5 = `
type ProofToken is Type:
  ProofToken{f: @n: Nat -> Nat}
def f(~p: Nat, n: Nat) -> Nat:
  match n:
    case Zero{}:
      p
    case Succ{x}:
      f(p, x)
def helper(b: Bool, p: Nat, ts: List<&1, ProofToken>, n: Nat) -> {f(p, n) == p : Nat}:
  match b:
    case False{}:
      match ts:
        case Nil{}:
          match n:
            case Zero{}: {==}
            case Succ{x}: helper(b, p, ts, x)
        case Con{head, tail}: helper(b, p, tail, n)
    case True{}:
      match ts:
        case Nil{}:
          match n:
            case Zero{}: {==}
            case Succ{x}: helper(b, p, ts, x)
        case Con{head, tail}: helper(b, p, tail, n)
def ordinary(n: Nat) -> Nat:
  f(3n, n)
def goal(n: Nat) -> Type:
  {ordinary(n) == 3n : Nat}
def theorem(n: Nat) -> goal(n):
  helper(True{}, 3n, Con{ProofToken{m => next = m; next}, Nil{}}, n)
`;

// R4 must reuse the checked nested specialization when C executes id(id(1)).
test('nested template interning preserves the checked value in C', async t => {
  const f = fixture(t);
  f.write('Main.bend', f.read('Main.bend').split('def resultado')[0] +
    'def intern(~p: Nat) -> Nat:\n  p\ndef main() -> Nat:\n  intern(intern(1n))\n');
  const admitted = await admitSubmission(f.manifest());
  assert.equal(admitted.report.primary, true);
  assert.equal(admitted.report.bendtt, true);
  assert.equal(runC(f.root, emitC(admitted), 'nested'), '1n');
});

// The certificate consumes a non-reflexive proof with Bool before recursive
// Nat cases and a list of linear functions. Generated transports must preserve
// the original descent tree and quantities.
test('private checked Book links structural evidence and emitted C', async t => {
  const f = fixture(t), { info } = await loadToolchain();

  const client = f.read('Client.bend')
    .replace('def programa()', 'def typed(~p: U32) -> U32:\n  p\n\ndef programa()')
    .replace('contar([1, 2, 3], 0)', 'contar([typed(1), typed(2), typed(3)], 0)');
  f.write('Client.bend', client + r5 +
    '\n# exact source: IO @unsafe ?todo 😀\n');
  f.bindCode();
  const motive = 'R.SegurancaPercurso(S.executar(n, Client.programa(), S.esquema(I.config()), s, I.contexto(), I.argumentos()), I.config(), s, I.contexto(), B.codigo(), I.argumentos())';
  f.write('ClientProof.bend', f.read('ClientProof.bend')
    .replace('import ./Bindings.bend as B', 'import ./Bindings.bend as B\nimport ./Client.bend as Client')
    .replace(/^( {6}| {10})L\.Ambos/gm, (_, indent) =>
      indent + '%Client.theorem(n): ' + motive + ';\n' + indent + 'L.Ambos'));
  const exactSource = f.read('Client.bend'), spawn = child.spawnSync, payloads = [];
  child.spawnSync = function (bin, args, options) {
    if (bin === info.verifier.kernelPath) payloads.push(fs.readFileSync(args[0], 'utf8'));
    return spawn(bin, args, options);
  };
  syncBuiltinESMExports();
  let admitted;
  try { admitted = await admitSubmission(f.manifest()); }
  finally { child.spawnSync = spawn; syncBuiltinESMExports(); }
  assert.equal(admitted.report.primary, true);
  assert.equal(admitted.report.bendtt, true);
  assert.equal('book' in admitted, false);
  assert.equal('tc' in admitted, false);
  assert.equal(admitted.sources.find(s => s.path === 'Client.bend').text, exactSource);
  assert.equal(payloads.length, 1);
  assert.match(payloads[0], /Evidence\.Client\.theorem\.original_target/);
  assert.match(payloads[0], /Evidence\.Client\.theorem\.evidence_source_link/);
  assert.match(payloads[0], /Bindings\.certificado\.actual_target/);
  assert.match(payloads[0], /Bindings\.termina\.actual_target/);
  const input = path.join(f.root, 'checked.bendtt');
  fs.writeFileSync(input, payloads[0]);
  const original = spawn(info.kernelPath, [input], { encoding: 'utf8', timeout: 60000 });
  assert.equal(original.status, 0, original.stdout + original.stderr);
  assert.equal(original.stdout.trim(), 'ALL PROOFS CHECK');
  assert.equal(admitted.report.verifier.correspondence.route, 'structural');
  assert.ok(admitted.report.instanceClosure.sourceLinks.includes('Bindings:certificado'));
  assert.ok(admitted.report.verifier.instances.some(k => k.startsWith('Client:f~')));
  // Sources can disappear after checking: emission uses the private checked Book.
  f.write('Client.bend', 'changed after admission');
  const c = emitC(admitted);
  assert.equal(emitC(admitted), c);
  assert.equal(runC(f.root, c, 'checked'), 'Dados.VInt{0, 6}');
});

function rawBook(B, code) {
  const book = B.book_nil();
  B.parse_book(book, B.BEND_DIR + '/', fs.readFileSync(B.BASE_BEND, 'utf8'), '', Object.create(null));
  for (const definition of Object.values(book.tlds)) definition.b = true;
  B.parse_book(book, '/tmp/', code, '', Object.create(null));
  B.book_valid(book);
  return book;
}

// A type-correct mutation to a live physical specialization must change C and
// be rejected. Checking must neither overwrite it nor prove a separate body.
test('physical specialization mutation is causally rejected', async t => {
  const { B, S, C, info } = await loadToolchain(), f = fixture(t);
  const code = 'def inner(~p: Nat) -> Nat:\n  p\ndef main() -> Nat:\n  inner(1n)\n' + r5;
  const book = rawBook(B, code);
  const checked = checkBook(S, book, info.verifier);
  assert.equal(checked.why, null);
  assert.equal(checked.correspondence.route, 'structural');
  assert.equal(runC(f.root, C.compile_book(book), 'before'), '1n');
  const name = [...book.tmps.inner.values()].find(k => book.tlds[k]);
  assert.ok(name);
  const changed = B.term_lower(B.Ann(B.Lit('Nat', 2), book.tlds[name].T));
  book.tlds[name].e = changed;
  assert.equal(runC(f.root, C.compile_book(book), 'changed'), '2n');
  const result = checkBook(S, book, info.verifier);
  assert.match(result.why, /source_link/);
  assert.doesNotMatch(result.why, /parse error|out of fuel/i);
  assert.equal(book.tlds[name].e, changed);
});
