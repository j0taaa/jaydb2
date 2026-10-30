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

// The unmodified official kernel must preserve acceptance and refusal.
test('official kernel accepts a proof and rejects a false one', t => {
  for (const [term, accepted] of [['ok', true], ['wrong', false]]) {
    const result = checkKernelFile(input(t, `unit : <ok> = .${term}\n`), info);
    assert.equal(result.why === null, accepted);
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
    safe_emit(_book, file) { fs.writeFileSync(file, ''); return ['unsupported typed representation']; },
  };
  assert.throws(() => checkBook(unsupported, {}, info),
    error => error instanceof VerifierInfrastructure && /representation out of scope/.test(error.message));
});
