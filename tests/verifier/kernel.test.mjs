import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import child from 'node:child_process';
import { validateVerifier, checkBook, checkKernelFile, startBookCheck, VerifierInfrastructure } from '../../tools/verifier/check.mjs';

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

// This tests our CLI-result mapping, using the pinned kernel's exact format.
test('official fuel exhaustion is infrastructure, not a false certificate', t => {
  const file = input(t, 'unit : <ok> = .ok\n'), spawn = child.spawnSync;
  try {
    for (const why of ['In proof:\nout of fuel', 'out of fuel', 'In proof:\nexpected: <out of fuel>\nobserved: .wrong']) {
      child.spawnSync = (_bin, _args, options) => {
        fs.writeSync(options.stdio[1], 'SOME PROOFS FAIL\n' + why + '\n');
        return { status: 1 };
      };
      if (why.endsWith('\nout of fuel') || why === 'out of fuel') {
        assert.throws(() => checkKernelFile(file, info), e => e instanceof VerifierInfrastructure && /out of fuel/.test(e.message));
      } else assert.equal(checkKernelFile(file, info).why, why);
    }
  } finally { child.spawnSync = spawn; }
});


// The concurrent path retains exact verdict parsing and reaps/cleans children.
test('asynchronous kernel checks the fixed payload and removes its private input', async () => {
  for (const [term, accepted] of [['ok', true], ['wrong', false]]) {
    let input;
    const translator = { safe_emit(_book, file) {
      input = file;
      fs.writeFileSync(file, `unit : <ok> = .${term}\n`);
      return [];
    } };
    const result = await startBookCheck(translator, {}, info);
    assert.equal(result.error, undefined);
    assert.equal(result.value.why === null, accepted);
    assert.equal(fs.existsSync(path.dirname(input)), false);
  }
});

test('asynchronous kernel spawn failure is infrastructure and cleans its input', async t => {
  const kernel = input(t, '');
  fs.writeFileSync(kernel, fs.readFileSync(info.kernelPath));
  fs.chmodSync(kernel, 0o600); // Correct pinned bytes, deliberately not executable.
  let translated;
  const result = await startBookCheck({ safe_emit(_book, file) {
    translated = file; fs.writeFileSync(file, 'unit : <ok> = .ok\n'); return [];
  } }, {}, { ...info, kernelPath: kernel });
  assert.ok(result.error instanceof VerifierInfrastructure);
  assert.match(result.error.message, /EACCES/);
  assert.equal(fs.existsSync(path.dirname(translated)), false);
});
