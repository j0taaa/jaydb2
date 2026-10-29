import test from 'node:test';
import assert from 'node:assert/strict';
import child from 'node:child_process';
import { syncBuiltinESMExports } from 'node:module';
import { admitSubmission, emitC, preflight, AdmissionError, bootstrapInfo } from '../../tools/admission/index.mjs';
import { fixture } from './helpers.mjs';

const rejected = (manifest, codes) => assert.rejects(admitSubmission(manifest), error =>
  error instanceof AdmissionError && codes.includes(error.code));

// A changed behavior cannot reuse a certificate for the previous program.
test('wrong supplied proof is rejected by the primary checker', async t => {
  const f = fixture(t);
  f.write('Client.bend', f.read('Client.bend').replace('contar([1, 2, 3], 0)', 'contar([1, 2, 4], 0)'));
  f.bindCode();
  await rejected(f.manifest(), ['PRIMARY_CHECK']);
});

// Admission scans unused definitions too; purity is independent of reachability.
test('unused IO, foreign code, unsafe definitions and holes are rejected', async t => {
  for (const [body, code] of [
    ['def hidden() -> IO(Unit):\n  IO.exit(91)\n', 'IO'],
    ['def hidden() -> IO(Unit):\n  import "./external.c"\n', 'FOREIGN'],
    ['@unsafe\ndef hidden(n: Nat) -> Nat:\n  hidden(n)\n', 'UNSAFE'],
    ['def hidden() -> Unit:\n  ?todo\n', 'META'],
    ['law invented:\n  Empty\n', 'OPEN_LAW'],
  ]) {
    const f = fixture(t);
    f.write('Client.bend', f.read('Client.bend') + '\n' + body);
    f.bindCode();
    await rejected(f.manifest(), [code]);
  }
});

// The certificate must bind the exact source, target and authorized proof file.
test('source, target and proof-authority substitutions are rejected', async t => {
  const source = fixture(t);
  source.write('Client.bend', source.read('Client.bend') + '\n# different bytes\n');
  await rejected(source.manifest(), ['SOURCE_BINDING']);
  const target = fixture(t);
  target.write('Bindings.bend', target.read('Bindings.bend').replace(
    'R.Certifica(I.config(), codigo(), Client.programa(), I.contexto(), I.argumentos())', 'Unit'));
  await rejected(target.manifest(), ['TARGET']);
  const authority = fixture(t), manifest = authority.manifest();
  manifest.openTargets['Bindings:certificado'] = 'Client.bend';
  await rejected(manifest, ['REDEFINITION']);
});

// Registered bytes and dependency closure are the trust boundary before parsing.
test('hash mismatch, missing dependency and import cycle fail before checking', async t => {
  const changed = fixture(t), manifest = changed.manifest();
  changed.write('Instance.bend', changed.read('Instance.bend') + '\n');
  await rejected(manifest, ['HASH']);
  for (const [header, code] of [
    ['import ./Unregistered.bend as Hidden\n', 'DEPENDENCY'],
    ['import ./Client.bend as Self\n', 'IMPORT_CYCLE'],
  ]) {
    const f = fixture(t);
    f.write('Client.bend', header + f.read('Client.bend'));
    f.bindCode();
    await rejected(f.manifest(), [code]);
  }
});

// A proof cannot acquire host state by using an otherwise pure helper.
test('private host capture is rejected', async t => {
  const f = fixture(t);
  f.write('Private.bend', 'import Base\ndef secret() -> String:\n  "private state"\n', 'host');
  f.write('ClientProof.bend', 'import ./Private.bend as Secret\n' + f.read('ClientProof.bend') +
    '\ndef hidden() -> Unit:\n  (x => Unit{})(Secret.secret())\n');
  await rejected(f.manifest(), ['HOST_CAPTURE']);
});

// A kernel execution failure is a technical failure, never a mathematical verdict.
test('kernel infrastructure failure cannot admit a submission', async t => {
  const f = fixture(t), spawn = child.spawnSync;
  child.spawnSync = function (bin, args, options) {
    if (bin === bootstrapInfo().verifier.kernelPath) return { status: null, signal: 'SIGKILL' };
    return spawn(bin, args, options);
  };
  syncBuiltinESMExports();
  try { await rejected(f.manifest(), ['BENDTT_INFRASTRUCTURE']); }
  finally { child.spawnSync = spawn; syncBuiltinESMExports(); }
});

// A public report/source record cannot forge the private checked-Book handle.
test('preflight preserves bytes and emission requires an authentic handle', t => {
  const f = fixture(t);
  assert.equal(preflight(f.manifest()).records.get('Client.bend').text, f.read('Client.bend'));
  assert.throws(() => emitC({ sources: [], report: { primary: true, bendtt: true } }),
    error => error.code === 'BOOK_CHANGED');
});
