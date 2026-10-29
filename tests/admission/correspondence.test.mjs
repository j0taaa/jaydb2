import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import child from 'node:child_process';
import { admitSubmission, emitC } from '../../tools/admission/index.mjs';
import { loadToolchain } from '../../tools/admission/bootstrap.mjs';
import { bookFingerprint, closeEmissionBook } from '../../tools/admission/book-graph.mjs';
import { prepareClosedInstances } from '../../tools/admission/closed-instances.mjs';
import { checkBook } from '../../tools/verifier/check.mjs';
import { fixture } from './helpers.mjs';

function tagFixture(t) {
  const f = fixture(t);
  f.write('Main.bend', f.read('Main.bend').split('def resultado')[0] + `
type Tag is Data:
  One{}
  Two{}
def keep(~p: Nat) -> Nat:
  p
def use() -> Nat:
  keep(1n)
def main() -> Tag:
  One{}
law correct:
  {main() == One{} : Tag}
def correct():
  {==}
`);
  return f;
}
function runC(t, root, c, name) {
  const file = path.join(root, name + '.c'), bin = path.join(root, name);
  fs.writeFileSync(file, c);
  const cc = child.spawnSync('/usr/bin/clang-19', ['-O1', '-w', file, '-o', bin, '-lm', '-pthread'], { encoding: 'utf8', timeout: 60000 });
  assert.equal(cc.status, 0, cc.stderr);
  const run = child.spawnSync(bin, [], { encoding: 'utf8', timeout: 10000 });
  assert.equal(run.status, 0, run.stderr);
  return run.stdout.trim();
}

test('construtores preservam identidade, ordem e metadados entre prova e C', async t => {
  const f = tagFixture(t);
  const control = await admitSubmission(f.manifest());
  const c = emitC(control);
  assert.equal(runC(t, f.root, c, 'control'), 'One{}');
  assert.equal(emitC(control), c);
  assert.throws(() => control.book.tlds.Tag.c.reverse(), TypeError);
  assert.throws(() => { control.book.tlds.Tag.c[0].k = 'Two'; }, TypeError);
  for (const mutate of [
    a => { a.book.tlds.Tag.c[0] = a.book.tlds.Tag.c[1]; },
    a => a.book.tlds.Tag.c.reverse(),
    a => { a.book.tlds.Tag.c[0].k = 'Two'; a.book.tlds.Tag.c[1].k = 'One'; },
    a => { a.book.tlds.Tag.c[0].n = 1; },
    a => a.book.tlds.Tag.c.splice(0, 1),
    a => { a.book.ctrs.One.k = 'Two'; },
    a => { a.book.tlds.main.e.x.k = 'Two'; },
  ]) {
    const a = await admitSubmission(f.manifest());
    mutate(a);
    assert.throws(() => emitC(a), e => e.code === 'BOOK_CHANGED');
  }
});

test('mapas de instâncias e valores de memo não escapam ao selo', async t => {
  const { B } = await loadToolchain();
  const f = tagFixture(t);
  const a = await admitSubmission(f.manifest());
  const variants = a.book.tmps.keep;
  assert.ok(variants.size);
  const [key] = variants.keys();
  variants.set(key, 'not-checked');
  assert.throws(() => emitC(a), e => e.code === 'BOOK_CHANGED');
  const b = await admitSubmission(f.manifest());
  const c = emitC(b);
  assert.equal(emitC(b), c);
  assert.throws(() => b.book.tmps.keep.set('extra', 'unchecked'), /verification/);
  Map.prototype.set.call(b.book.tmps.keep, 'extra', 'unchecked');
  assert.throws(() => emitC(b), e => e.code === 'BOOK_CHANGED');
  const d = await admitSubmission(f.manifest());
  emitC(d);
  const cell = d.book.tlds.main.e.T;
  assert.equal(cell.$, 'Var');
  assert.ok(cell.v);
  cell.v = B.Ref('Empty');
  assert.throws(() => emitC(d), e => e.code === 'BOOK_CHANGED');
});

test('fingerprint e freeze cobrem Map/Set e arrays residuais sem ignorar conteúdo', async () => {
  const { B } = await loadToolchain();
  const book = B.book_nil();
  book.tlds.A = { $: 'Def', n: 0, x: 0, T: B.ADT('D', [], undefined, ['One']), v: B.Ctr('One', []),
    metadata: { map: new Map([['tag', { name: 'One' }]]), set: new Set(['One']) } };
  const first = bookFingerprint(B, book);
  book.tlds.A.metadata.map.get('tag').name = 'Two';
  assert.notEqual(bookFingerprint(B, book), first);
  const second = bookFingerprint(B, book);
  book.tlds.A.metadata.set.add('Two');
  assert.notEqual(bookFingerprint(B, book), second);
  const third = bookFingerprint(B, book);
  book.tlds.A.T.r[0] = 'Two';
  assert.notEqual(bookFingerprint(B, book), third);
  closeEmissionBook(B, book);
  assert.throws(() => book.tlds.A.metadata.map.set('new', 'tag'), /verification/);
  assert.throws(() => book.tlds.A.metadata.set.add('Three'), /verification/);
  assert.throws(() => { book.tlds.A.metadata.map.get('tag').name = 'Three'; }, TypeError);
  assert.throws(() => book.tlds.A.T.r.push('Three'), TypeError);
});

test('protótipos e metadados opcionais não mudam nat_add entre prova e C', async t => {
  const { B } = await loadToolchain();
  const f = fixture(t);
  f.write('Main.bend', f.read('Main.bend').split('def resultado')[0] + `
def nat_add(a: Nat, b: Nat) -> Nat:
  0n
def main() -> Nat:
  nat_add(1n, 2n)
law correct:
  {main() == 0n : Nat}
def correct():
  {==}
`);
  const a = await admitSubmission(f.manifest());
  const def = a.book.tlds.nat_add, proto = Object.getPrototypeOf(def);
  const before = bookFingerprint(B, a.book);
  for (const inherited of [{ b: true }, Object.create({ b: true }), Object.defineProperty({}, 'b', { value: true })]) {
    Object.setPrototypeOf(def, inherited);
    assert.notEqual(bookFingerprint(B, a.book), before);
    assert.throws(() => emitC(a), e => e.code === 'BOOK_CHANGED');
    Object.setPrototypeOf(def, proto);
  }
  // Non-enumerable own metadata also participates, rather than only spread.
  Object.defineProperty(def, 'b', { value: true, configurable: true });
  assert.throws(() => emitC(a), e => e.code === 'BOOK_CHANGED');
  delete def.b;
  const c = emitC(a);
  assert.equal(runC(t, f.root, c, 'prototype-control'), '0n');
  assert.equal(emitC(a), c);
  assert.throws(() => Object.setPrototypeOf(def, { b: true }), TypeError);
});

test('Object.prototype opcional e métodos herdados continuam selados após freeze', async t => {
  const f = tagFixture(t), a = await admitSubmission(f.manifest());
  const reject = (object, key, value) => {
    const original = Object.getOwnPropertyDescriptor(object, key);
    try {
      Object.defineProperty(object, key, { value, configurable: true, writable: true });
      assert.throws(() => emitC(a), e => e.code === 'BOOK_CHANGED');
    } finally {
      if (original) Object.defineProperty(object, key, original);
      else delete object[key];
    }
  };
  reject(Object.prototype, 'b', true);
  reject(Object.prototype, 'i', ['not-checked.c']);
  // Fingerprinting must not run an inherited serialization hook.
  let calls = 0;
  reject(Object.prototype, 'toJSON', () => { calls++; return 'same'; });
  assert.equal(calls, 0);
  const c = emitC(a);
  reject(Object.prototype, 'b', true);
  reject(Array.prototype, Symbol.iterator, function* () { yield 'unchecked'; });
  reject(Map.prototype, 'get', () => 'unchecked');
  assert.equal(emitC(a), c);
});

function rawBook(B, code) {
  const book = B.book_nil();
  B.parse_book(book, B.BEND_DIR + '/', fs.readFileSync(B.BASE_BEND, 'utf8'), '', Object.create(null));
  for (const d of Object.values(book.tlds)) d.b = true;
  B.parse_book(book, '/tmp/', code, '', Object.create(null));
  try { B.book_valid(book); } catch (error) { throw new Error(error.$ === 'Err' ? B.err_show(error) : error.message); }
  return book;
}
const verify = (S, book, info) => checkBook(S, book, info.verifier, { deadlineNs: (process.hrtime.bigint() + 20000000000n).toString() });

test('igualdade direta chama o mesmo físico de main, inclusive depois de mutação tipável', async t => {
  const { B, S, C, info } = await loadToolchain();
  const f = fixture(t);
  const code = 'def inner(~p: Nat) -> Nat:\n  p\ndef main() -> Nat:\n  inner(1n)\nlaw direct:\n  {inner(1n) == 1n : Nat}\ndef direct():\n  {==}\n';
  const positive = rawBook(B, code);
  assert.equal(verify(S, positive, info).why, null);
  const name = [...positive.tmps.inner.values()].find(k => positive.tlds[k]);
  assert.equal(B.term_lower(positive.tlds.direct.T).a.k, name);
  const text = path.join(f.root, 'closed.bendtt');
  S.admission_safe_emit(positive, text);
  assert.doesNotMatch(fs.readFileSync(text, 'utf8'), /^inner\.q/m, 'closed calls cannot receive a separate logical specialization');
  const before = runC(t, f.root, C.compile_book(positive), 'before');
  const changed = rawBook(B, code);
  const actual = [...changed.tmps.inner.values()].find(k => changed.tlds[k]);
  const body = B.term_lower(B.Ann(B.Lit('Nat', 2), changed.tlds[actual].T));
  changed.tlds[actual].e = body;
  const got = verify(S, changed, info);
  assert.ok(got.why);
  assert.equal(changed.tlds[actual].e, body, 'closure cannot erase the existing physical mutation');
  const after = runC(t, f.root, C.compile_book(changed), 'after');
  assert.notEqual(before, after);
});

test('chamada somente em igualdade é elaborada antes de ambos checkers finais', async t => {
  const f = tagFixture(t);
  f.write('Main.bend', f.read('Main.bend') + '\ndef erased_only(~p: Nat) -> Nat:\n  p\nlaw only_in_type:\n  {erased_only(7n) == 7n : Nat}\ndef only_in_type():\n  {==}\n');
  const a = await admitSubmission(f.manifest());
  assert.ok(a.report.instanceClosure.created.some(k => k.startsWith('erased_only~')));
  assert.ok(a.report.verifier.instances.some(k => k.startsWith('erased_only~')));
  assert.ok(a.report.instanceClosure.sourceLinks.some(k => k.startsWith('erased_only~')));
  const names = Object.keys(a.book.tlds);
  const c = emitC(a);
  assert.equal(emitC(a), c);
  assert.deepEqual(Object.keys(a.book.tlds), names);
});

test('chaves distintas mas convertíveis não escondem corpo físico divergente', async () => {
  const { B, S, info } = await loadToolchain();
  const code = `def inner(~p: Nat) -> Nat:
  p
def main() -> Nat:
  inner(1n)
def alias() -> Nat:
  Nat.add(1n, 0n)
def other() -> Nat:
  inner(alias())
law direct:
  {inner(Nat.add(1n, 0n)) == 1n : Nat}
def direct():
  {==}
`;
  const positive = rawBook(B, code);
  assert.equal(verify(S, positive, info).why, null);
  const changed = rawBook(B, code);
  const actual = changed.tmps.inner.get(B.term_key(B.Lit('Nat', 1)));
  changed.tlds[actual].e = B.term_lower(B.Ann(B.Lit('Nat', 2), changed.tlds[actual].T));
  assert.ok(verify(S, changed, info).why, 'the real physical body must be rejected, by the law or its origin guard');
});

test('instância de template da base também fica vinculada ao corpo oficial', async () => {
  const { B, S, info } = await loadToolchain();
  const code = `def inc(n: Nat) -> Nat:
  Nat.add(n, 1n)
def main() -> List<Nat>:
  List.map(Nat, Nat, inc, [1n])
`;
  const positive = rawBook(B, code);
  assert.equal(verify(S, positive, info).why, null);
  const changed = rawBook(B, code);
  const name = [...changed.tmps['List.map'].values()].find(k => changed.tlds[k]);
  assert.ok(name);
  const T = changed.tlds[name].T;
  changed.tlds[name].e = B.term_lower(B.Ann(B.Lam('xs', 0, () => B.Ctr('Nil', [])), T));
  assert.match(verify(S, changed, info).why, /source_link/);
});

test('fechamento prospectivo resolve argumento que só fica fechado por conversão', async () => {
  const { B, S, info } = await loadToolchain();
  const book = rawBook(B, `def ignore(-n: Nat) -> Nat:
  1n
def inner(~p: Nat) -> Nat:
  p
law direct:
  for n: Nat
  {inner(ignore(n)) == 1n : Nat}
def direct(n):
  {==}
`);
  assert.equal(prepareClosedInstances(B, book).created.length, 0, 'the argument is not syntactically closed');
  const closed = S.admission_prepare_book(book);
  const name = closed.created.find(k => k.startsWith('inner~'));
  assert.ok(name, 'the real translator must discover and elaborate the closed normal form');
  assert.equal(verify(S, book, info).why, null);
  book.tlds[name].e = B.term_lower(B.Ann(B.Lit('Nat', 2), book.tlds[name].T));
  assert.ok(verify(S, book, info).why);
});
