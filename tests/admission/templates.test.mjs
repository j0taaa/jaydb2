import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import child from 'node:child_process';
import { admitSubmission, emitC, preflight } from '../../tools/admission/index.mjs';
import { loadToolchain } from '../../tools/admission/bootstrap.mjs';
import { checkBook, VerifierInfrastructure, VerifierDeadline } from '../../tools/verifier/check.mjs';
import { fixture, repo } from './helpers.mjs';

const proofType = '@a: Nat -> {Nat.is_ge(a, a) == True{} : Bool}';
const proofCode = `
def witness(a: Nat) -> {Nat.is_ge(a, a) == True{} : Bool}:
  Nat.ge_refl(a)
def proof_identity(~p: ${proofType}) -> ${proofType}:
  p
def instantiated(a: Nat) -> {Nat.is_ge(a, a) == True{} : Bool}:
  proof_identity(witness, a)
`;
const add = (t, code) => {
  const f = fixture(t);
  f.write('Client.bend', f.read('Client.bend') + '\n' + code);
  f.bindCode();
  return f;
};
const deadline = () => (process.hrtime.bigint() + 20000000000n).toString();

const dependentDomain = `
def f(~p: Nat, n: Nat) -> Nat:
  match n:
    case Zero{}:
      p
    case Succ{x}:
      x
def g(~p: Nat, ~q: @n: Nat -> {f(p, n) == f(p, n) : Nat}) -> Unit:
  Unit{}
def used() -> Unit:
  g(1n, n => {==})
`;

for (const [name, code] of [
  ['binder local no domínio de ~q', dependentDomain],
  ['cabeçalho dependente exposto por conversão e recursão', `
def f(~p: Nat, n: Nat) -> Nat:
  match n:
    case Zero{}:
      p
    case Succ{x}:
      f(p, x)
def domain(~p: Nat) -> Type:
  @n: Nat -> {f(p, n) == f(p, n) : Nat}
def g(~p: Nat, ~q: domain(p)) -> Unit:
  Unit{}
def outer(~p: Nat, ~q: domain(p)) -> Unit:
  g(p, q)
def used() -> Unit:
  outer(1n, n => {==})
`],
  ['domínios ~A/~p sem habitante global', `
def f(~A: Type, ~p: A, n: Nat) -> A:
  match n:
    case Zero{}:
      p
    case Succ{x}:
      f(A, p, x)
def g(~A: Type, ~p: A, ~q: @n: Nat -> {f(A, p, n) == f(A, p, n) : A}) -> Unit:
  Unit{}
def used() -> Unit:
  g(Nat, 1n, n => {==})
`],
]) {
  test(`domínio simbólico conserva primário, kernel e fechamento físico: ${name}`, async t => {
    const f = add(t, code);
    f.write('Main.bend', f.read('Main.bend').split('def resultado')[0] + '\ndef main() -> Unit:\n  Client.used()\n');
    const a = await admitSubmission({ ...f.manifest(), verification: { deadlineNs: deadline() } });
    assert.equal(a.report.primary, true);
    assert.equal(a.report.bendtt, true);
    assert.ok(a.report.verifier.schemas.includes('Client:f'));
    assert.ok(a.report.verifier.schemas.includes('Client:g'));
    const actual = a.report.verifier.instances.filter(k => k.startsWith('Client:g~'));
    assert.ok(actual.length);
    for (const k of actual) assert.ok(a.report.instanceClosure.sourceLinks.includes(k));
    assert.ok(!Object.keys(a.book.tlds).some(k => /~[Apq]$/.test(k)), 'symbolic binders cannot leak into the global Book');
    const names = Object.keys(a.book.tlds), c = emitC(a);
    assert.equal(emitC(a), c);
    assert.deepEqual(Object.keys(a.book.tlds), names);
    fs.writeFileSync(path.join(f.root, 'dependent.c'), c);
    const built = child.spawnSync('/usr/bin/clang-19', ['-O1', '-w', 'dependent.c', '-o', 'dependent', '-lm', '-pthread'], { cwd: f.root, encoding: 'utf8', timeout: 60000 });
    assert.equal(built.status, 0, built.stderr);
    const ran = child.spawnSync(path.join(f.root, 'dependent'), [], { encoding: 'utf8', timeout: 10000 });
    assert.equal(ran.status, 0, ran.stderr);
    assert.equal(ran.stdout.trim(), 'Unit{}');
  });
}

test('headers simbólicos não provam False num domínio dependente', async t => {
  const f = add(t, dependentDomain.replace('-> Unit:\n  Unit{}', '-> {0n == 1n : Nat}:\n  {==}'));
  await assert.rejects(admitSubmission(f.manifest()), e => e.code === 'PRIMARY_CHECK');
});

test('domínio simbólico não encobre alterações das instâncias físicas f/g', async t => {
  const { B, S, info } = await loadToolchain();
  const f = add(t, dependentDomain + '\nlaw actual:\n  {f(1n, 0n) == 1n : Nat}\ndef actual():\n  {==}\n');
  const good = primaryBook(B, f);
  assert.equal(checkBook(S, good, info.verifier, { deadlineNs: deadline() }).why, null);
  for (const prefix of ['Client:f~', 'Client:g~']) {
    const book = primaryBook(B, f);
    S.admission_prepare_book(book, { deadlineNs: deadline() });
    const name = Object.keys(book.tlds).find(k => k.startsWith(prefix));
    assert.ok(name);
    const def = book.tlds[name];
    def.e = B.term_lower(B.Ann(prefix === 'Client:f~' ? B.Lam('n', 0, () => B.Lit('Nat', 2)) : B.Rfl(), def.T));
    const changed = def.e;
    const got = checkBook(S, book, info.verifier, { deadlineNs: deadline() });
    assert.ok(got.why);
    assert.ok(BigInt(got.attempts) > 0n);
    assert.equal(def.e, changed, 'preparation cannot replace a divergent physical body');
  }
});

function primaryBook(B, f) {
  const book = B.book_nil();
  B.parse_book(book, B.BEND_DIR + '/', fs.readFileSync(B.BASE_BEND, 'utf8'), '', Object.create(null));
  for (const def of Object.values(book.tlds)) def.b = true;
  for (const r of preflight(f.manifest()).ordered) B.parse_book(book, f.root + '/', r.body, r.ns, r.aliases);
  B.book_valid(book);
  return book;
}

// The source proof is neither searched for nor globally assumed. In particular
// Void and dependent ~A/~x have no closed model to select for the schema.
test('templates simbólicos, provas explícitas e dependências: ambos checkers e C real', async t => {
  const f = add(t, proofCode + `
type Void is Type:
def impossible_identity(~p: Void) -> Void:
  p
def dependent(~A: Type, ~x: A) -> A:
  x
def repeated(~p: ${proofType}) -> ({Nat.is_ge(1n, 1n) == True{} : Bool} & {Nat.is_ge(2n, 2n) == True{} : Bool}):
  (p(1n), p(2n))
def id(~p: Nat) -> Nat:
  p
law reducible:
  for ~p: Nat
  {id(p) == p : Nat}
def reducible(p):
  {==}
def recursive(~p: ${proofType}, n: Nat) -> Nat:
  match n:
    case Zero{}:
      Zero{}
    case Succ{x}:
      Succ{recursive(p, x)}
def real_recursive(n: Nat) -> Nat:
  recursive(witness, n)
def selected(~p: Bool) -> U32:
  Bool.pick(U32, p, 6, 9)
law actual_parameter:
  {selected(True{}) == 6 : U32}
def actual_parameter():
  {==}
`);
  const source = f.read('Client.bend');
  const selectedStart = source.indexOf('def selected(');
  const selectedEnd = source.indexOf('law actual_parameter:', selectedStart);
  const selected = source.slice(selectedStart, selectedEnd);
  f.write('Client.bend', (source.slice(0, selectedStart) + source.slice(selectedEnd)).replace('def programa()', selected + '\ndef programa()').replace('contar([1, 2, 3], 0)', 'selected(True{})'));
  f.bindCode();
  const a = await admitSubmission({ ...f.manifest(), verification: { initialModelFuel: '1', initialFuel: '1', deadlineNs: deadline() } });
  assert.equal(a.report.primary, true);
  assert.equal(a.report.bendtt, true);
  assert.ok(a.report.verifier.schemas.includes('Client:impossible_identity'));
  assert.ok(a.report.verifier.schemas.includes('Client:dependent'));
  for (const k of Object.keys(a.book.tlds).filter(k => k.startsWith('Client:') && k.includes('~'))) {
    assert.ok(a.report.verifier.instances.includes(k), `live root missing: ${k}`);
  }
  assert.ok(a.report.verifier.instances.some(k => k.startsWith('Client:proof_identity~')));
  const names = Object.keys(a.book.tlds);
  const c = emitC(a);
  assert.deepEqual(Object.keys(a.book.tlds), names);
  assert.throws(() => { a.book.tlds.unchecked = a.book.tlds['Client:programa']; }, /verification/);
  assert.throws(() => { a.book.tmps['Client:proof_identity'].set('new instance', 'unchecked'); }, /verification/);
  fs.writeFileSync(path.join(f.root, 'program.c'), c);
  const built = child.spawnSync('/usr/bin/clang-19', ['-O1', '-w', 'program.c', '-o', 'program', '-lm', '-pthread'], { cwd: f.root, encoding: 'utf8', timeout: 60000 });
  assert.equal(built.status, 0, built.stderr);
  const ran = child.spawnSync(path.join(f.root, 'program'), [], { encoding: 'utf8', timeout: 10000 });
  assert.equal(ran.status, 0, ran.stderr);
  assert.equal(ran.stdout.trim(), 'Dados.VInt{0, 6}');
});

test('ordem dos construtores não exige inventar um modelo para ~p', async t => {
  const levels = 18;
  let code = 'type Hard0 is Data:\n';
  for (let i = 1; i <= levels; i++) code += `type Hard${i} is Data:\n  Left${i}{child: Hard${i - 1}}\n  Right${i}{child: Hard${i - 1}}\n`;
  for (let i = 1; i <= levels; i++) code += `type Chain${i} is Data:\n  Link${i}{child: ${i === 1 ? 'Unit' : 'Chain' + (i - 1)}}\n`;
  code += `type Search is Data:\n  DeadEnd{child: Hard${levels}}\n  Found{child: Chain${levels}}\ndef identity(~p: Search) -> Search:\n  p\n`;
  let witness = 'Unit{}';
  for (let i = 1; i <= levels; i++) witness = `Link${i}{${witness}}`;
  code += `def actual() -> Search:\n  identity(Found{${witness}})\n`;
  const f = add(t, code);
  const a = await admitSubmission({ ...f.manifest(), verification: { initialModelFuel: '1', deadlineNs: deadline() } });
  assert.equal(a.report.bendtt, true);
  assert.ok(a.report.verifier.instances.some(k => k.startsWith('Client:identity~')));
});

// Deliberately mutate an already-primary-checked instance, below the public
// mutation seal, to test the independent translation/kernel boundary itself.
test('schema válido não encobre prova falsa numa instância concreta', async t => {
  const { B, S, info } = await loadToolchain();
  const f = add(t, proofCode);
  const book = primaryBook(B, f);
  const name = Object.keys(book.tlds).find(k => k.startsWith('Client:proof_identity~'));
  assert.ok(name);
  const def = book.tlds[name];
  const T = B.term_wnf(book, def.T);
  def.e = B.term_lower(B.Ann(B.Lam('a', 0, a => B.Ann(B.Rfl(), T.B(a))), def.T));
  const got = checkBook(S, book, info.verifier, { initialFuel: '1', deadlineNs: deadline() });
  assert.ok(got.schemas.includes('Client:proof_identity'));
  assert.ok(got.instances.includes(name));
  assert.match(got.why, /unequal|equal|equation|reflex|expected|convert/i);
});

test('dependência de template após apagar ~p continua vinculada ao certificado real', async t => {
  const { B, S, info } = await loadToolchain();
  const f = add(t, `
def inner(~p: Nat) -> Nat:
  p
def outer(~p: Nat) -> Nat:
  inner(p)
def actual() -> Nat:
  outer(1n)
law dependent:
  {actual() == 1n : Nat}
def dependent():
  {==}
`);
  for (const target of ['Client:inner~', 'Client:outer~']) {
    const book = primaryBook(B, f);
    const name = Object.keys(book.tlds).find(k => k.startsWith(target));
    assert.ok(name);
    // Both 1 and 2 inhabit Nat. Only the original body satisfies dependent.
    book.tlds[name].e = B.term_lower(B.Ann(B.Lit('Nat', 2), book.tlds[name].T));
    const got = checkBook(S, book, info.verifier, { deadlineNs: deadline() });
    assert.ok(got.instances.includes(name));
    assert.match(got.why, /unequal|equal|equation|reflex|expected|convert/i);
  }
});

test('cadeia inner/outer no alvo Bindings.certificado não admite corpo físico falso', async t => {
  const { B, S, info } = await loadToolchain();
  const f = fixture(t);
  const claim = 'R.Certifica(I.config(), B.codigo(), Client.programa(), I.contexto(), I.argumentos())';
  const proof = f.read('ClientProof.bend').replace('import Base', 'import Base\nimport ./Client.bend as Client')
    .replace('def B.certificado(', `law body:\n  ${claim}\n\ndef body(`)
    .replace('def B.termina(', `def inner(~p: ${claim}) -> ${claim}:\n  p\n\ndef outer(~p: ${claim}) -> ${claim}:\n  inner(p)\n\ndef B.certificado(s, valido, identidade, n):\n  outer(body, s, valido, identidade, n)\n\ndef B.termina(`);
  f.write('ClientProof.bend', proof);
  const accepted = await admitSubmission({ ...f.manifest(), verification: { deadlineNs: deadline() } });
  assert.equal(accepted.report.bendtt, true);
  const refs = tree => {
    const found = new Set();
    const todo = [tree];
    while (todo.length) {
      const node = todo.pop();
      if (!node || typeof node !== 'object') continue;
      if (node.$ === 'Ref') found.add(node.k);
      for (const [key, value] of Object.entries(node)) if (key !== 's' && value && typeof value === 'object') todo.push(value);
    }
    return found;
  };
  for (const target of ['ClientProof:inner~', 'ClientProof:outer~']) {
    const book = primaryBook(B, f);
    const live = new Set(['Bindings:certificado']);
    for (const k of live) for (const ref of refs(book.tlds[k]?.e)) if (!live.has(ref)) live.add(ref);
    const name = [...live].find(k => k.startsWith(target) && book.tlds[k] !== undefined);
    assert.ok(name, `physical ${target} must occur in the certificate's actual checked tree closure`);
    assert.ok(accepted.report.verifier.instances.includes(name));
    book.tlds[name].e = B.term_lower(B.Ann(B.Rfl(), book.tlds[name].T));
    const got = checkBook(S, book, info.verifier, { initialFuel: '1', deadlineNs: deadline() });
    assert.ok(got.instances.includes(name));
    assert.ok(got.why, 'a valid Unit schema cannot replace the false physical certificate instance');
    assert.ok(BigInt(got.attempts) > 0n, 'the independent real kernel must reject the proof');
  }
});

for (const [name, code, expected] of [
  ['False no corpo', `def false_template(~p: Nat) -> {0n == 1n : Nat}:\n  {==}\n`, 'PRIMARY_CHECK'],
  ['outro template falso', `def false_inner(~p: Nat) -> {0n == 1n : Nat}:\n  {==}\ndef false_outer(~p: Nat) -> {0n == 1n : Nat}:\n  false_inner(p)\n`, 'PRIMARY_CHECK'],
  ['dependência apagada com efeito', `def erased(~p: Unit) -> Unit:\n  (x => Unit{})(IO.print("effect"))\n`, 'IO'],
  ['IO em template não usado', `def unused(~p: Nat) -> IO(Unit):\n  IO.print("effect")\n`, 'IO'],
  ['meta em template não usado', `def unused(~p: Nat) -> Unit:\n  (x => Unit{})(?proof)\n`, 'META'],
  ['unsafe em template não usado', `@unsafe\ndef unused(~p: Nat) -> Nat:\n  p\n`, 'UNSAFE'],
]) {
  test(`template conserva auditoria raw AST: ${name}`, async t => {
    const f = add(t, code);
    await assert.rejects(admitSubmission(f.manifest()), e => e.code === expected);
  });
}

test('modelo opaco distingue esgotamento, retenta sem teto e mantém deadline', async () => {
  const { B, S, info } = await loadToolchain();
  const book = B.book_nil();
  B.parse_book(book, B.BEND_DIR + '/', fs.readFileSync(B.BASE_BEND, 'utf8'), '', Object.create(null));
  for (const def of Object.values(book.tlds)) def.b = true;
  // A trusted foreign signature is permitted by the original primary. This
  // unit-level kernel test does not relax admission's foreign/IO barriers.
  B.parse_book(book, '/tmp/', 'type Search is Data:\n  Found{n: Nat}\ndef opaque() -> IO(Search):\n  import "./opaque.c"\n', '', Object.create(null));
  B.book_valid(book);
  const names = Object.keys(book.tlds);
  const got = checkBook(S, book, info.verifier, { initialModelFuel: '1', deadlineNs: deadline() });
  assert.equal(got.why, null);
  assert.ok(BigInt(got.modelAttempts) > 1n);
  assert.deepEqual(Object.keys(book.tlds), names);
  const full = checkBook(S, book, info.verifier, { deadlineNs: deadline() });
  assert.equal(got.inputSha256, full.inputSha256);
  assert.throws(() => checkBook(S, book, info.verifier, { initialModelFuel: '1', deadlineNs: process.hrtime.bigint().toString() }), e => e instanceof VerifierInfrastructure && /deadline/.test(e.message));
});

test('busca Safe real observa o deadline original e falha como infraestrutura', async () => {
  const { B, S, info } = await loadToolchain();
  const book = B.book_nil();
  B.parse_book(book, B.BEND_DIR + '/', fs.readFileSync(B.BASE_BEND, 'utf8'), '', Object.create(null));
  for (const def of Object.values(book.tlds)) def.b = true;
  let code = 'type Dead0 is Data:\n';
  for (let i = 1; i <= 18; i++) code += `type Dead${i} is Data:\n  L${i}{child: Dead${i - 1}}\n  R${i}{child: Dead${i - 1}}\n`;
  code += 'type Search is Data:\n  First{child: Dead18}\n  Last{unit: Unit}\ndef opaque() -> Search:\n  Last{Unit{}}\n';
  B.parse_book(book, '/tmp/', code, '', Object.create(null));
  B.book_valid(book);
  // At the private serializer boundary, make the inhabited definition opaque
  // to exercise its real exhaustive model search. Such an open declaration
  // remains forbidden by public admission; no production test hook is added.
  delete book.tlds.opaque.e;
  book.tlds.opaque.v = null;
  const start = process.hrtime.bigint();
  const deadlineNs = (start + 20000000n).toString();
  const seen = [];
  const observed = { ...S, admission_safe_emit(b, file, options) {
    seen.push(options.deadlineNs);
    assert.equal(b, book);
    return S.admission_safe_emit(b, file, options);
  } };
  assert.throws(() => checkBook(observed, book, info.verifier, { initialModelFuel: (1n << 50n).toString(), deadlineNs }), e =>
    e instanceof VerifierDeadline && e.code === 'HOST_VERIFICATION_DEADLINE' && e.cause instanceof S.SafeDeadlineExceeded);
  assert.ok(seen.length > 0);
  assert.ok(seen.every(value => value === deadlineNs));
  assert.ok(process.hrtime.bigint() - start < 2000000000n);
});

test('API e CLI propagam HOST_VERIFICATION_DEADLINE sem recusa matemática', async t => {
  const f = fixture(t);
  const manifest = { ...f.manifest(), verification: { deadlineNs: '1' } };
  await assert.rejects(admitSubmission(manifest), e => e.code === 'HOST_VERIFICATION_DEADLINE' && e.cause instanceof VerifierDeadline);
  const file = path.join(f.root, 'manifest.json');
  fs.writeFileSync(file, JSON.stringify(manifest));
  const got = child.spawnSync(process.execPath, [path.join(repo, 'tools/admission/cli.mjs'), '--manifest', file], { encoding: 'utf8', timeout: 10000 });
  assert.equal(got.status, 3, got.stderr);
  assert.equal(JSON.parse(got.stderr).code, 'HOST_VERIFICATION_DEADLINE');
});
