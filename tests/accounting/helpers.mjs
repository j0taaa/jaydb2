import { spawnSync } from 'node:child_process';
import assert from 'node:assert/strict';
const [kernel, book, source, object] = process.argv.slice(2);
const stages = [];
for (const [name, command, args, env] of [
  ['bendtt', kernel, [book], {...process.env, LEAN_STACK_SIZE_KB: '4194304'}],
  ['clang', '/usr/bin/clang-19', ['-x', 'c', '-c', source, '-o', object], process.env],
]) {
  const r = spawnSync(command, args, {encoding: 'utf8', env});
  assert.equal(r.error, undefined);
  assert.equal(r.signal, null);
  assert.equal(r.status, 0, r.stderr + r.stdout);
  stages.push({name, status: r.status, stdout: r.stdout.trim()});
}
console.log(JSON.stringify({pid: process.pid, stages}));
