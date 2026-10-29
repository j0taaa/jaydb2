import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import child from 'node:child_process';
import { admitSubmission, emitC } from '../../tools/admission/index.mjs';
import { loadToolchain } from '../../tools/admission/bootstrap.mjs';
import { bookFingerprint } from '../../tools/admission/book-graph.mjs';
import { checkBook } from '../../tools/verifier/check.mjs';
import { fixture, repo } from './helpers.mjs';

const cases = path.join(repo, 'tests/admission/cases/v4');
const source = name => fs.readFileSync(path.join(cases, name + '.bend'), 'utf8');
const deadline = () => (process.hrtime.bigint() + 30000000000n).toString();
const options = () => ({ deadlineNs: deadline() });
function rawBook(B, code) {
  const book = B.book_nil();
  B.parse_book(book, B.BEND_DIR + '/', fs.readFileSync(B.BASE_BEND, 'utf8'), '', Object.create(null));
  for (const d of Object.values(book.tlds)) d.b = true;
  B.parse_book(book, '/tmp/', code.replace(/^import Base\s*\n/, ''), '', Object.create(null));
  B.book_valid(book);
  return book;
}

for (const name of ['recursive_proof', 'recursive_uninstantiated', 'recursive_proof_nonrecursive',
  'recursive_proof_runtime_f', 'recursive_proof_no_template', 'conversion_minimal',
  'conversion_concrete_control', 'source_link_recursive_alias', 'source_link_nonrecursive_control',
  'source_link_lambda_control', 'ordinary_domain']) {
  test(`equações e conversão conservam exemplo oficial: ${name}`, async t => {
    // These are the literal official fixtures from independent review V4.
    const official = child.spawnSync(path.join(repo, '.tools/bend-2.0.39/bin/bend'),
      [path.join(cases, name + '.bend'), '--check-only'], { encoding: 'utf8', timeout: 30000 });
    assert.equal(official.status, 0, official.stdout + official.stderr);
    assert.match(official.stdout, /ALL PROOFS CHECK/);
    const f = fixture(t);
    f.write('Client.bend', f.read('Client.bend') + '\n' + source(name).replace(/^import Base\s*\n/, ''));
    f.bindCode();
    const admitted = await admitSubmission({ ...f.manifest(), verification: options() });
    assert.equal(admitted.report.primary, true);
    assert.equal(admitted.report.bendtt, true);
    const inventory = Object.keys(admitted.book.tlds), c = emitC(admitted);
    assert.equal(emitC(admitted), c);
    assert.deepEqual(Object.keys(admitted.book.tlds), inventory);
    for (const k of admitted.report.verifier.instances)
      assert.ok(admitted.report.instanceClosure.sourceLinks.includes(k), 'each physical alias keeps its origin guard');
  });
}

test('fechamento para por estado estável mesmo com reescrita reconstruída pelo primário', async () => {
  const { B, S, info } = await loadToolchain();
  const book = rawBook(B, source('conversion_minimal'));
  const resource = options();
  S.admission_prepare_book(book, resource);
  const before = bookFingerprint(B, book), names = Object.keys(book.tlds);
  B.book_valid(book);
  const ordered = new Set(book.order);
  for (const [k, d] of Object.entries(book.tlds))
    if (d.$ === 'Def' && !d.b && d.e !== undefined && !ordered.has(k)) d.e = B.def_check(book, k, d);
  const final = S.admission_prepare_book(book, resource);
  assert.ok(final.rewrites > 0, 'the checker really rebuilt an annotation');
  assert.equal(bookFingerprint(B, book), before);
  assert.deepEqual(Object.keys(book.tlds), names);
  assert.equal(checkBook(S, book, info.verifier, resource).why, null);
});

test('aliases físicos existentes preservam corpos, equações e guards separados', async () => {
  const { B, S, info } = await loadToolchain();
  const make = () => {
    const book = rawBook(B, source('source_link_recursive_alias'));
    S.admission_prepare_book(book, options());
    const [literalKey, physical] = [...book.tmps.f].find(([, k]) => book.tlds[k]);
    const alias = 'f~existing';
    const annotated = B.term_key(B.term_lower(B.Ann(B.Lit('Nat', 3), B.Ref('Nat'))));
    // An older elaboration/opaque phase may have produced both representatives.
    // Neither declaration may be merged or have its body replaced afterwards.
    book.tmps.f.set(annotated, alias);
    book.tlds[alias] = { ...book.tlds[physical] };
    assert.equal(B.admission_instance(book, 'f', [B.term_higher(JSON.parse(literalKey))]), physical);
    assert.equal(B.admission_instance(book, 'f', [B.term_higher(JSON.parse(annotated))]), alias);
    return { book, physical, alias };
  };
  const good = make(), bodies = [good.book.tlds[good.physical].e, good.book.tlds[good.alias].e];
  const accepted = checkBook(S, good.book, info.verifier, options());
  assert.equal(accepted.why, null);
  assert.ok(accepted.instances.includes(good.physical));
  assert.ok(accepted.instances.includes(good.alias));
  assert.equal(good.book.tlds[good.physical].e, bodies[0]);
  assert.equal(good.book.tlds[good.alias].e, bodies[1]);
  for (const which of ['physical', 'alias']) {
    const bad = make(), d = bad.book.tlds[bad[which]];
    d.e = B.term_lower(B.Ann(B.Lam('n', 0, () => B.Lit('Nat', 2)), d.T));
    const changed = d.e;
    assert.match(checkBook(S, bad.book, info.verifier, options()).why, /source_link/);
    assert.equal(d.e, changed);
  }
});

test('corpo simbólico falso não ganha as equações da fonte por hipótese', async t => {
  const f = fixture(t);
  const invalid = source('recursive_proof').replace('case Zero{}:\n      p', 'case Zero{}:\n      0n');
  f.write('Client.bend', f.read('Client.bend') + '\n' + invalid.replace(/^import Base\s*\n/, ''));
  f.bindCode();
  await assert.rejects(admitSubmission(f.manifest()), e => e.code === 'PRIMARY_CHECK');
  // The independent gate must also check an UNUSED symbolic body, rather than
  // silently dropping schemas and relying on physical instances/source links.
  const { B, S, info } = await loadToolchain();
  const book = rawBook(B, source('recursive_uninstantiated'));
  assert.ok(!book.tmps.f?.size);
  const d = book.tlds.f;
  const T = B.All(B.Lone(), 'n', 0, B.Ref('Nat'), () => B.Ref('Nat'));
  d.e = B.term_lower(B.Ann(B.Lam('n', 0, () => B.Lit('Nat', 2)), T));
  const altered = d.e;
  const got = checkBook(S, book, info.verifier, options());
  assert.match(got.why, /proof\.(?:template_body|compile_schema)/);
  assert.ok(BigInt(got.attempts) > 0n);
  assert.equal(d.e, altered);
});
