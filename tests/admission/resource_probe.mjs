// Isolated process used by the launcher/OS-resource integration tests.
import fs from 'node:fs';
import child from 'node:child_process';
import { fixture, repo } from './helpers.mjs';
import { admitSubmission } from '../../tools/admission/index.mjs';
import { sha256, toolchainLock } from '../../tools/admission/bootstrap.mjs';

const cleanups = [];
const f = fixture({ after: fn => cleanups.push(fn) });
const scenario = process.argv[2];
try {
  if (scenario === 'deep' || scenario === 'deep-false') {
    f.write('Client.bend', f.read('Client.bend') + '\ndef deep() -> Nat:\n  ' + '('.repeat(10000) + '0n' + ')'.repeat(10000) + '\n');
    if (scenario === 'deep-false') f.write('Client.bend', f.read('Client.bend') + '\nlaw wrong:\n  {0n == 1n : Nat}\ndef wrong():\n  {==}\n');
  } else if (scenario === 'template-depth') {
    const chain = Array.from({ length: 80 }, (_, i) => `def nest${i}(~f: U32 -> U32, x: U32) -> U32:\n  ${i === 0 ? 'f(x)' : `nest${i - 1}(f, x)`}\n`).join('\n');
    f.write('Client.bend', f.read('Client.bend') + '\n' + chain + '\ndef identity(x: U32) -> U32:\n  x\ndef use() -> U32:\n  nest79(identity, 6)\n');
  } else if (scenario === 'template-width') {
    f.write('Client.bend', f.read('Client.bend') + '\ndef pick(~s: String, x: U32) -> U32:\n  x\ndef use() -> U32:\n  pick("' + 'a'.repeat(40000) + '", 6)\n');
  }
  f.bindCode();
  let baseline;
  if (scenario === 'template-depth' || scenario === 'template-width') {
    const binary = repo + '.tools/bend-2.0.39/bin/bend';
    if (sha256(fs.readFileSync(binary)) !== toolchainLock.officialBinarySha256) throw new Error('Baseline compiler hash mismatch');
    const old = child.spawnSync(binary, [f.root + '/Main.bend', '--check-only'], {
      encoding: 'utf8', timeout: 20000, env: { ...process.env, BEND_NO_TELEMETRY: '1' },
    });
    baseline = old.stdout + old.stderr;
    if (old.status !== 1) throw new Error('Baseline compiler did not reproduce the resource guard: ' + baseline);
  }
  const got = await admitSubmission({ ...f.manifest(),
    verification: { initialFuel: scenario === 'low-fuel' ? '1' : '400000000' } });
  console.log(JSON.stringify({ primary: got.report.primary, bendtt: got.report.bendtt,
    baseline, attempts: got.report.verifier.attempts, frontendResourcesSha256: got.report.frontendResourcesSha256 }));
} catch (e) {
  console.error(JSON.stringify({ code: e.code, phase: e.phase, message: e.message }));
  process.exitCode = 2;
} finally { for (const cleanup of cleanups) cleanup(); }
