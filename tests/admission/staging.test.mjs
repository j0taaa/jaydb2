import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import child from 'node:child_process';
import { syncBuiltinESMExports } from 'node:module';
import os from 'node:os';
import path from 'node:path';
import { initialize } from '../../tools/service/stage.mjs';

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
