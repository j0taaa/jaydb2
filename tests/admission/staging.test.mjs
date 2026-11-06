import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
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
