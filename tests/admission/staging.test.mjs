import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import child from 'node:child_process';
import { syncBuiltinESMExports } from 'node:module';
import os from 'node:os';
import path from 'node:path';
import { initialize, execute } from '../../tools/service/stage.mjs';
import { fixture as submissionFixture } from './helpers.mjs';
import { admitSubmission } from '../../tools/admission/index.mjs';

function fixture(t) {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'jaydb-seed-guard-'));
  t.after(() => fs.rmSync(root, { recursive: true, force: true }));
  const seed = path.join(root, 'Initial.bend'), config = path.join(root, 'Configuration.bend');
  fs.writeFileSync(seed, 'import Base\ndef private_marker() -> String: "private seed bytes"\n');
  return { root, seed, config, work: path.join(root, 'work') };
}

test('seed aliases are rejected before public staging, including hardlinks and transitive imports', t => {
  for (const kind of ['direct', 'symlink', 'hardlink', 'transitive-hardlink']) {
    const f = fixture(t), alias = path.join(f.root, 'Alias.bend');
    if (kind === 'symlink') fs.symlinkSync(f.seed, alias);
    else if (kind !== 'direct') fs.linkSync(f.seed, alias);
    let dependency = kind === 'direct' ? 'Initial.bend' : 'Alias.bend';
    if (kind === 'transitive-hardlink') {
      fs.writeFileSync(path.join(f.root, 'Helper.bend'), 'import ./Alias.bend as Hidden\n');
      dependency = 'Helper.bend';
    }
    fs.writeFileSync(f.config, `import ./${dependency} as Hidden\n`);
    assert.throws(() => initialize(f.work, f.config, f.seed, '/unused-bend', '/unused-kernel'),
      e => e.code === 'DEPENDENCY' && e.message.includes('private seed'), kind);
    assert.equal(fs.existsSync(path.join(f.work, 'public')), false, kind);
  }
});

test('public dependencies cannot claim the reserved Seed namespace', t => {
  const f = fixture(t);
  fs.writeFileSync(path.join(f.root, 'Seed.bend'), 'import Base\ndef public_marker() -> Unit: Unit{}\n');
  fs.writeFileSync(f.config, 'import ./Seed.bend as Public\n');
  assert.throws(() => initialize(f.work, f.config, f.seed, '/unused-bend', '/unused-kernel'),
    e => e.code === 'DEPENDENCY' && e.message.includes('reserved module: Seed.bend'));
  assert.equal(fs.existsSync(path.join(f.work, 'public')), false);
});

// These guards run before compilation; a mock compiler only supplies the
// positive control proving legal graphs are not rejected by discovery.
test('administrator cycles reject before staging, including growing directory aliases', t => {
  for (const kind of ['direct', 'mutual', 'directory-alias', 'private-alias']) {
    const f = fixture(t);
    fs.symlinkSync(f.root, path.join(f.root, 'again'), 'dir');
    if (kind === 'direct') fs.writeFileSync(f.config, 'import ./Configuration.bend as Self\n');
    if (kind === 'mutual') {
      fs.writeFileSync(f.config, 'import ./Peer.bend as Peer\n');
      fs.writeFileSync(path.join(f.root, 'Peer.bend'), 'import ./Configuration.bend as Back\n');
    }
    if (kind === 'directory-alias') fs.writeFileSync(f.config, 'import ./again/Configuration.bend as Self\n');
    if (kind === 'private-alias') {
      fs.writeFileSync(f.config, 'import Base\n');
      fs.writeFileSync(f.seed, 'import ./again/Initial.bend as Self\n');
    }
    assert.throws(() => initialize(f.work, f.config, f.seed, '/unused-bend', '/unused-kernel'),
      e => e.code === 'IMPORT_CYCLE', kind);
    assert.equal(fs.existsSync(path.join(f.work, 'public')), false, kind);
  }
});

test('shared diamonds and finite hardlink chains still reach compilation', t => {
  for (const kind of ['diamond', 'hardlinks']) {
    const f = fixture(t), expected = new Map();
    const put = (name, body) => {
      const file = path.join(f.root, name);
      fs.mkdirSync(path.dirname(file), { recursive: true });
      fs.writeFileSync(file, body); expected.set(name, body);
    };
    if (kind === 'diamond') {
      put('Configuration.bend', 'import ./Left.bend as Left\nimport ./Right.bend as Right\n');
      put('Left.bend', 'import ./Shared.bend as Shared\n');
      put('Right.bend', 'import ./Shared.bend as Shared\n');
      put('Shared.bend', 'import Base\n');
    } else {
      put('Configuration.bend', 'import ./Entry.bend as Entry\n');
      put('Entry.bend', 'import ./nested/Entry.bend as Next\n');
      fs.mkdirSync(path.join(f.root, 'nested'));
      fs.linkSync(path.join(f.root, 'Entry.bend'), path.join(f.root, 'nested/Entry.bend'));
      expected.set('nested/Entry.bend', expected.get('Entry.bend'));
      put('nested/nested/Entry.bend', 'import Base\n');
    }
    const original = child.spawnSync;
    let calls = 0;
    child.spawnSync = () => { calls++; return { status: 37 }; };
    syncBuiltinESMExports();
    try {
      assert.throws(() => initialize(f.work, f.config, f.seed, '/unused-bend', '/unused-kernel'),
        e => e.code === 'HELPER', kind);
      assert.equal(calls, 1, kind);
      for (const [name, body] of expected)
        assert.equal(fs.readFileSync(path.join(f.work, 'public', name), 'utf8'), body, name);
    } finally {
      child.spawnSync = original;
      syncBuiltinESMExports();
    }
  }
});

test('prepared and read-only contract dependencies survive the production public staging closure', t => {
  const f = fixture(t);
  fs.writeFileSync(f.config, 'import ./PreparedLaws.bend as Prepared\n' +
    'import ./ReadOnlyContract.bend as ReadContract\nimport ./ReadOnly.bend as ReadOnly\n');
  const original = child.spawnSync;
  let calls = 0;
  child.spawnSync = (_program, args) => {
    calls++;
    const manifest = JSON.parse(fs.readFileSync(args[2], 'utf8'));
    const staged = new Set(manifest.dependencies.map(dependency => dependency.path));
    for (const name of ['PreparedLaws.bend', 'PreparedProtocol.bend', 'PreparedRegistry.bend',
      'ReadOnlyContract.bend', 'ReadOnly.bend']) assert.ok(staged.has(name), name);
    for (const dependency of manifest.dependencies) {
      const source = fs.readFileSync(path.join(manifest.submissionDir, dependency.path), 'utf8');
      assert.doesNotMatch(source, /^import\s+\.\.\//m, dependency.path);
    }
    return { status: 37 };
  };
  syncBuiltinESMExports();
  try {
    assert.throws(() => initialize(f.work, f.config, f.seed, '/unused-bend', '/unused-kernel'),
      error => error.code === 'HELPER');
    assert.equal(calls, 1, 'the complete closure must reach the compiler boundary');
  } finally {
    child.spawnSync = original;
    syncBuiltinESMExports();
  }
});

test('the frozen recovery descriptor retains exact public, tooling and controller bytes without the private seed', t => {
  const f = fixture(t), privateText = 'seed-only-' + path.basename(f.root);
  fs.writeFileSync(f.seed, `import Base\ndef secret() -> String: "${privateText}"\n`);
  fs.writeFileSync(f.config, 'import ./Helper.bend as Helper\n');
  fs.writeFileSync(path.join(f.root, 'Helper.bend'), 'import Base\n# original helper\n');
  const original = child.spawnSync;
  child.spawnSync = () => ({ status: 37 });
  syncBuiltinESMExports();
  const decode = work => {
    const descriptor = fs.readFileSync(path.join(work, 'environment.bytes'));
    const magic = Buffer.from('jaydb2-environment-v1\n');
    assert.deepEqual(descriptor.subarray(0, magic.length), magic);
    let position = magic.length;
    const take = () => {
      assert.ok(descriptor.length - position >= 8);
      const length = descriptor.readBigUInt64BE(position); position += 8;
      assert.ok(length <= BigInt(descriptor.length - position));
      const bytes = descriptor.subarray(position, position + Number(length));
      position += Number(length); return bytes;
    };
    const entries = [];
    while (position < descriptor.length) entries.push([take().toString('utf8'), take()]);
    assert.equal(position, descriptor.length);
    assert.deepEqual(entries.map(([name]) => name), entries.map(([name]) => name).sort());
    assert.equal(new Set(entries.map(([name]) => name)).size, entries.length);
    assert.equal(descriptor.includes(Buffer.from(privateText)), false);
    const values = new Map(entries);
    assert.equal(values.has('public/Seed.bend'), false);
    assert.equal(values.has('public/Environment.bend'), false, 'the derived identity is excluded to avoid self reference');
    for (const [name, bytes] of entries) {
      const actual = name === 'server/controller' ? fs.readFileSync(`/proc/${process.ppid}/exe`)
        : fs.readFileSync(path.join(work, name));
      assert.deepEqual(bytes, actual, name);
    }
    return { descriptor, values };
  };
  try {
    assert.throws(() => initialize(f.work, f.config, f.seed, '/unused-bend', '/unused-kernel'), e => e.code === 'HELPER');
    const first = decode(f.work);
    const again = path.join(f.root, 'again');
    assert.throws(() => initialize(again, f.config, f.seed, '/unused-bend', '/unused-kernel'), e => e.code === 'HELPER');
    assert.deepEqual(decode(again).descriptor, first.descriptor, 'temporary paths do not change environment identity');
    fs.writeFileSync(path.join(f.root, 'Helper.bend'), 'import Base\n# modified helper\n');
    const changed = path.join(f.root, 'changed');
    assert.throws(() => initialize(changed, f.config, f.seed, '/unused-bend', '/unused-kernel'), e => e.code === 'HELPER');
    const last = decode(changed);
    assert.notDeepEqual(last.descriptor, first.descriptor);
    assert.equal(last.values.get('public/Helper.bend').toString('utf8'), 'import Base\n# modified helper\n');
  } finally {
    child.spawnSync = original;
    syncBuiltinESMExports();
  }
});


// Freeze only, deliberately stopping before native compilation. The exact
// generated pure manifest is then checked by BOTH real official admission
// tools after the compiler stub is restored; no accepted report is mocked.
test('prepared target substitution preserves matching client comments and literals', async t => {
  const target = 'R.Certifies(I.config(), code(), Client.program(), I.context(), I.arguments())';
  for (const purpose of ['prepare', 'prepare-read']) for (const kind of ['comment', 'literal']) {
    const f = fixture(t), submission = submissionFixture(t);
    const originalInstance = submission.read('Instance.bend');
    fs.writeFileSync(f.config, originalInstance.split('\ndef context()')[0]);
    submission.write('Instance.bend', 'import ./Configuration.bend as C\n' +
      originalInstance.slice(0, originalInstance.indexOf('def NotObserves')) +
      'def config() -> S.Configuration:\n  C.config()\n' + originalInstance.slice(originalInstance.indexOf('\ndef context()')));
    submission.write('Client.bend', submission.read('Client.bend') + (kind === 'comment'
      ? '\n# harmless source text: ' + target + '\n'
      : '\ndef source_marker() -> String:\n  ' + JSON.stringify(target) + '\n'));
    submission.bindCode();
    submission.write('ClientProof.bend', submission.read('ClientProof.bend').replace(
      'def B.certificate(s, valid, identity, n):', 'def B.certificate(ctx, args, s, valid, identity, n):') +
      (purpose === 'prepare-read' ? '\ndef B.read_only(ctx, args):\n  (1n, Unit{})\n' : ''));
    const code = submission.read('Client.bend'), proof = submission.read('ClientProof.bend');
    const original = child.spawnSync;
    child.spawnSync = () => ({ status: 37 }); syncBuiltinESMExports();
    try {
      assert.throws(() => initialize(f.work, f.config, f.seed, '/unused-bend', '/unused-kernel'), e => e.code === 'HELPER');
    } finally { child.spawnSync = original; syncBuiltinESMExports(); }
    const output = path.join(f.root, 'prepared');
    let reachedCompiler = 0, pureManifest;
    child.spawnSync = (_program, args) => {
      reachedCompiler++; pureManifest = JSON.parse(fs.readFileSync(args.at(-1), 'utf8'));
      return { status: 37 };
    };
    syncBuiltinESMExports();
    try {
      assert.throws(() => execute(f.work, output, submission.root, '/unused-bend', '/unused-kernel', purpose), e => e.code === 'HELPER', purpose + ':' + kind);
      assert.equal(reachedCompiler, 1, purpose + ':' + kind);
    } finally { child.spawnSync = original; syncBuiltinESMExports(); }
    assert.equal(fs.readFileSync(path.join(output, 'Client.bend'), 'utf8'), code);
    assert.equal(fs.readFileSync(path.join(output, 'ClientProof.bend'), 'utf8'), proof);
    const admitted = await admitSubmission(pureManifest);
    assert.equal(admitted.report.primary, true);
    assert.equal(admitted.report.bendtt, true);
    assert.equal(admitted.report.certificateMode, 'universal');
    assert.equal(admitted.report.readOnly, purpose === 'prepare-read');
  }
});
