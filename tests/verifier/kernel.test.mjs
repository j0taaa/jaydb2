import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import child from 'node:child_process';
import { validateVerifier, checkKernelFile, VerifierInfrastructure } from '../../tools/verifier/check.mjs';

const info = validateVerifier();
function input(t, text) {
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), 'jaydb-verifier-test-'));
  t.after(() => fs.rmSync(directory, { force: true, recursive: true }));
  const file = path.join(directory, 'proof.bendtt');
  fs.writeFileSync(file, text);
  return file;
}

test('kernel real: orçamento inicial insuficiente é ampliado e prova verdadeira passa', t => {
  const file = input(t, 'unit : <ok> = .ok\n');
  const small = child.spawnSync(info.kernelPath, [file, '1'], { encoding: 'utf8' });
  assert.equal(small.status, 75, small.stdout + small.stderr);
  const got = checkKernelFile(file, info, { initialFuel: '1' });
  assert.equal(got.why, null);
  assert.ok(BigInt(got.attempts) > 1n);
});

test('kernel real: ampliar fuel conserva a recusa de uma prova falsa', t => {
  const file = input(t, 'unit : <ok> = .wrong\n');
  const got = checkKernelFile(file, info, { initialFuel: '1' });
  assert.match(got.why, /a label of <ok>/);
  assert.ok(BigInt(got.attempts) > 1n);
});

test('campo apagado não exporta sua testemunha como prova viva', t => {
  const erased = `dead : Σ-p : <> -> <()> =
  (-({λ{(,): λ-p => λu => p} : ∀b : Σ-p : <> -> <()> -> <>} dead), ())
`;
  // The original kernel permits a witness solely inside an erased field.
  assert.equal(checkKernelFile(input(t, erased), info).why, null);
  const leak = erased + `escaped : <> =
  ({λ{(,): λ-p => λu => p} : ∀b : Σ-p : <> -> <()> -> <>} dead)
`;
  assert.match(checkKernelFile(input(t, leak), info).why, /affine live code/);
});

test('kernel real: exaustão de weak head não é mismatch de tipo', t => {
  const aliases = Array.from({ length: 80 }, (_, i) => `T${i} : *1 = ${i === 0 ? '∀x:<ok> -> <ok>' : 'T' + (i - 1)}`).join('\n');
  const file = input(t, aliases + '\nid : T79 = λx => x\n');
  const small = child.spawnSync(info.kernelPath, [file, '32'], { encoding: 'utf8' });
  assert.equal(small.status, 75, small.stdout + small.stderr);
  assert.equal(checkKernelFile(file, info, { initialFuel: '32' }).why, null);
});

test('fuel é Nat exato além de uint64 e do limite antigo, sem coerção JS', t => {
  const amount = (1n << 90n).toString();
  const got = checkKernelFile(input(t, 'unit : <ok> = .ok\n'), info, { initialFuel: amount });
  assert.equal(got.why, null);
  assert.equal(got.fuel, amount);
});

test('deadline único vence durante trabalho real e produz infraestrutura', t => {
  const file = input(t, Array.from({ length: 25000 }, (_, i) => `v${i} : <ok> = .ok`).join('\n'));
  const start = process.hrtime.bigint();
  assert.throws(() => checkKernelFile(file, info, {
    initialFuel: '1', deadlineNs: (start + 10000000n).toString(),
  }), e => e instanceof VerifierInfrastructure && /deadline|ETIMEDOUT|timed out/i.test(e.message));
  assert.ok(process.hrtime.bigint() - start < 2000000000n);
});

test('deadline Nat enorme omite timer local inexato e conserva aceitação real', t => {
  const got = checkKernelFile(input(t, 'unit : <ok> = .ok\n'), info,
    { deadlineNs: '1' + '0'.repeat(5000) });
  assert.equal(got.why, null);
});

test('provas genéricas mantêm os axiomas da fonte oficial', () => {
  for (const theorem of ['book_check', 'consistent', 'adequate']) {
    assert.ok(info.proofLog.includes(`@${theorem} : ∀ [inst : FuelBudget]`));
    assert.ok(info.proofLog.includes(`'${theorem}' depends on axioms: [propext, Classical.choice, Quot.sound]`));
  }
  assert.doesNotMatch(info.proofLog, /sorryAx/);
});
