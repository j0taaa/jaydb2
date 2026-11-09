import test from 'node:test';
import assert from 'node:assert/strict';
import child from 'node:child_process';
import fs from 'node:fs';
import { syncBuiltinESMExports } from 'node:module';
import { admitSubmission, emitC, preflight, AdmissionError, bootstrapInfo } from '../../tools/admission/index.mjs';
import { fixture } from './helpers.mjs';

const rejected = (manifest, codes) => assert.rejects(admitSubmission(manifest), error =>
  error instanceof AdmissionError && codes.includes(error.code));

// A changed behavior cannot reuse a certificate for the previous program.
test('wrong supplied proof is rejected by the primary checker', async t => {
  const f = fixture(t);
  f.write('Client.bend', f.read('Client.bend').replace('count([1, 2, 3], 0)', 'count([1, 2, 4], 0)'));
  f.bindCode();
  await rejected(f.manifest(), ['PRIMARY_CHECK']);
});

test('malformed source retains the official parse rejection', async t => {
  const f = fixture(t);
  f.write('Client.bend', f.read('Client.bend') + '\ndef malformed( -> Unit:\n  Unit{}\n');
  f.bindCode();
  await rejected(f.manifest(), ['PARSE']);
});

test('frontend setup IO failure is infrastructure, not a false certificate', async t => {
  const f = fixture(t), manifest = f.manifest();
  await admitSubmission(manifest); // The identical source has a valid derivation.
  const base = fs.realpathSync(bootstrapInfo().sourceDir + '/bend2/base.bend');
  const read = fs.readFileSync;
  const failure = Object.assign(new Error('injected Base read EIO'), { code: 'EIO' });
  let baseReads = 0;
  fs.readFileSync = function (file, ...args) {
    // Bootstrap validates the pinned bytes first; the second read is the
    // actual admission setup immediately before parsing those same bytes.
    if (file === base && ++baseReads === 2) throw failure;
    return read.call(this, file, ...args);
  };
  syncBuiltinESMExports();
  try {
    await assert.rejects(admitSubmission(manifest), error =>
      error instanceof AdmissionError && error.code === 'FRONTEND_INFRASTRUCTURE'
      && error.phase === 'parse' && error.cause === failure
      && error.message.includes(failure.message));
    assert.equal(baseReads, 2, 'the fault must reach the real Base parsing boundary');
  } finally {
    fs.readFileSync = read;
    syncBuiltinESMExports();
  }
});

test('unexpected primary frontend faults are infrastructure, retaining the cause', async t => {
  const f = fixture(t), manifest = f.manifest();
  await admitSubmission(manifest);
  for (const failure of [new Error('injected primary allocation failure'),
    Object.assign(new TypeError('injected malformed diagnostic marker'), { $: 'Err' })]) {
    const set = Map.prototype.set;
    let injected = 0;
    Map.prototype.set = function (key, value) {
      // The pinned book_valid begins by constructing the declaration-order
      // Map. Inject there without modifying the tool or its checked Book.
      if (!injected && new Error().stack?.includes('at Module.book_valid (')) {
        injected++;
        throw failure;
      }
      return set.call(this, key, value);
    };
    try {
      await assert.rejects(admitSubmission(manifest), error =>
        error instanceof AdmissionError && error.code === 'FRONTEND_INFRASTRUCTURE'
        && error.phase === 'primary' && error.cause === failure
        && error.message.includes(failure.message));
      assert.equal(injected, 1, 'the fault must reach the real primary checker');
    } finally {
      Map.prototype.set = set;
    }
  }
});

// Admission scans unused definitions too; purity is independent of reachability.
test('unused IO, foreign code, unsafe definitions and holes are rejected', async t => {
  for (const [body, code] of [
    ['def hidden() -> IO(Unit):\n  IO.exit(91)\n', 'IO'],
    ['def hidden() -> IO(Unit):\n  import "./external.c"\n', 'FOREIGN'],
    ['@unsafe\ndef hidden(n: Nat) -> Nat:\n  hidden(n)\n', 'UNSAFE'],
    ['def hidden() -> Unit:\n  ?all\n', 'META'],
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
    'R.Certifies(I.config(), code(), Client.program(), I.context(), I.arguments())', 'Unit'));
  await rejected(target.manifest(), ['TARGET']);
  const authority = fixture(t), manifest = authority.manifest();
  manifest.openTargets['Bindings:certificate'] = 'Client.bend';
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

test('universal targets reject concrete substitution and transitive captured values', async t => {
  const prepare = () => {
    const f = fixture(t);
    f.write('Bindings.bend', f.read('Bindings.bend').replace(
      'R.Certifies(I.config(), code(), Client.program(), I.context(), I.arguments())',
      '@ctx: D.Context -> @args: D.Value -> R.Certifies(I.config(), code(), Client.program(), ctx, args)'));
    f.write('ClientProof.bend', f.read('ClientProof.bend').replace(
      'def B.certificate(s, valid, identity, n):', 'def B.certificate(ctx, args, s, valid, identity, n):'));
    f.write('Bindings.bend', f.read('Bindings.bend') + '\ndef proof_source() -> String:\n  ' +
      JSON.stringify(f.read('ClientProof.bend')) + '\n');
    return f;
  };
  const concrete = fixture(t);
  await rejected({ ...concrete.manifest(), certificateMode: 'universal' }, ['TARGET']);
  const f = prepare();
  const admitted = await admitSubmission({ ...f.manifest(), certificateMode: 'universal' });
  assert.equal(admitted.report.certificateMode, 'universal');
  const source = prepare();
  source.write('Client.bend', source.read('Client.bend') + '\n# new source\n');
  await rejected({ ...source.manifest(), certificateMode: 'universal' }, ['SOURCE_BINDING']);
  const proofSource = prepare();
  proofSource.write('ClientProof.bend', proofSource.read('ClientProof.bend') + '\n# different proof bytes\n');
  await rejected({ ...proofSource.manifest(), certificateMode: 'universal' }, ['SOURCE_BINDING']);
  for (const captured of ['context', 'arguments']) {
    const g = prepare();
    // A library alias and a generic helper cannot launder a concrete host
    // value. Audit runs both before and after official checked specializations.
    g.write('Capture.bend', `import Base\nimport ./Instance.bend as Alias\nimport ./Data.bend as D\n` +
      `def capture(~A: Type, x: A) -> D.${captured === 'context' ? 'Context' : 'Value'}:\n  Alias.${captured}()\n`, 'library');
    g.write('Client.bend', 'import ./Capture.bend as Indirect\n' + g.read('Client.bend') +
      `\ndef hidden() -> D.${captured === 'context' ? 'Context' : 'Value'}:\n  Indirect.capture(Unit, Unit{})\n`);
    g.bindCode();
    await rejected({ ...g.manifest(), certificateMode: 'universal' }, ['HOST_CAPTURE']);
  }
});

// A kernel execution failure is a technical failure, never a mathematical verdict.
test('kernel infrastructure failure cannot admit a submission', async t => {
  const f = fixture(t), spawn = child.spawnSync;
  // The official loader canonicalizes the allowed immutable .tools symlink.
  const kernel = fs.realpathSync(bootstrapInfo().verifier.kernelPath);
  let injected = 0;
  child.spawnSync = function (bin, args, options) {
    if (bin === kernel) { injected++; return { status: null, signal: 'SIGKILL' }; }
    return spawn(bin, args, options);
  };
  syncBuiltinESMExports();
  try {
    await rejected(f.manifest(), ['BENDTT_INFRASTRUCTURE']);
    assert.ok(injected > 0, 'fault hook must intercept the actual official kernel');
  }
  finally { child.spawnSync = spawn; syncBuiltinESMExports(); }
});

// A translated-payload rejection after primary acceptance is a disagreement
// in the checking pipeline, not proof that the original certificate is false.
test('primary acceptance followed by kernel rejection is infrastructure', async t => {
  const f = fixture(t);
  await admitSubmission(f.manifest()); // Same source succeeds without the fault.
  const spawn = child.spawnSync;
  const kernel = fs.realpathSync(bootstrapInfo().verifier.kernelPath);
  const why = 'In valid_source:\n- expected: AllEntries.qv_2\n- observed: AllEntries.qv_1';
  let injected = 0;
  child.spawnSync = function (bin, args, options) {
    if (bin === kernel) {
      injected++;
      fs.writeSync(options.stdio[1], 'SOME PROOFS FAIL\n' + why + '\n');
      return { status: 1 };
    }
    return spawn(bin, args, options);
  };
  syncBuiltinESMExports();
  try {
    await assert.rejects(admitSubmission(f.manifest()), error =>
      error instanceof AdmissionError && error.code === 'BENDTT_INFRASTRUCTURE'
      && error.message.includes(why));
    assert.ok(injected > 0, 'the primary checker must reach the actual kernel boundary');
  } finally {
    child.spawnSync = spawn;
    syncBuiltinESMExports();
  }
});

// A public report/source record cannot forge the private checked-Book handle.
test('preflight preserves bytes and emission requires an authentic handle', t => {
  const f = fixture(t);
  const source = '\uFEFF' + f.read('Client.bend');
  f.write('Client.bend', source);
  f.bindCode();
  assert.equal(preflight(f.manifest()).records.get('Client.bend').text, f.read('Client.bend'));
  assert.throws(() => emitC({ sources: [], report: { primary: true, bendtt: true } }),
    error => error.code === 'BOOK_CHANGED');
});
