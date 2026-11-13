import test from 'node:test';
import assert from 'node:assert/strict';
import child from 'node:child_process';
import { repo } from './helpers.mjs';

// Same diagnostic gate as make verify: mutation of real implementation bodies,
// original universal law, and only `false` fails in both pinned checker modes.
test('implementation mutations break the actual universal laws in both checkers', () => {
  const result = child.spawnSync('python3', ['-B', 'tests/proof/test_proofs.py', '--implementation-mutations-only'],
    { cwd: repo, encoding: 'utf8', timeout: 600_000 });
  assert.equal(result.status, 0, result.stdout + result.stderr);
  assert.match(result.stdout, /3 fixtures, 6 official-mode rejections/);
});
