import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { validateVerifier, checkBook, checkKernelFile, VerifierInfrastructure } from '../../tools/verifier/check.mjs';

const info = validateVerifier();
function input(t, text) {
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), 'jaydb-kernel-'));
  t.after(() => fs.rmSync(directory, { recursive: true, force: true }));
  const file = path.join(directory, 'proof.bendtt');
  fs.writeFileSync(file, text);
  return file;
}

// Increasing development fuel must preserve both acceptance and refusal.
test('fuel retries preserve the real kernel verdict', t => {
  for (const [term, accepted] of [['ok', true], ['wrong', false]]) {
    const result = checkKernelFile(input(t, `unit : <ok> = .${term}\n`), info, { initialFuel: '1' });
    assert.equal(result.why === null, accepted);
    assert.ok(BigInt(result.attempts) > 1n);
    if (!accepted) assert.match(result.why, /a label of <ok>/);
  }
});

// An erased witness cannot be duplicated into live proof code.
test('erased fields cannot export a live witness', t => {
  const erased = 'dead : Σ-p : <> -> <()> =\n  (-({λ{(,): λ-p => λu => p} : ∀b : Σ-p : <> -> <()> -> <>} dead), ())\n';
  assert.equal(checkKernelFile(input(t, erased), info).why, null);
  const leak = erased + 'escaped : <> =\n  ({λ{(,): λ-p => λu => p} : ∀b : Σ-p : <> -> <()> -> <>} dead)\n';
  assert.match(checkKernelFile(input(t, leak), info).why, /affine live code/);
});

// Missing translation support must not be mislabeled as a false certificate.
test('unsupported representation is infrastructure', () => {
  const unsupported = {
    admission_safe_emit() { return { oos: ['unsupported typed representation'], schemas: [], instances: [] }; },
    SafeResourceExhausted: class extends Error {}, SafeDeadlineExceeded: class extends Error {},
  };
  assert.throws(() => checkBook(unsupported, {}, info),
    error => error instanceof VerifierInfrastructure && /representation unsupported/.test(error.message));
});
