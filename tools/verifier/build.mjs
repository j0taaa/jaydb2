#!/usr/bin/env node
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import child from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { deriveKernel, LEAN_VERSION, sha256 } from './derive.mjs';
import { useGrowingMainStack } from './main.mjs';

const root = fileURLToPath(new URL('../../', import.meta.url));
const lock = JSON.parse(fs.readFileSync(new URL('../admission/toolchain.lock.json', import.meta.url)));

export function derivedInfo(sourceDir = path.join(root, '.tools/bend-source-' + lock.version)) {
  const original = fs.readFileSync(path.join(sourceDir, 'bend2/bendtt.lean'));
  if (sha256(original) !== lock.files['bend2/bendtt.lean']) throw new Error('Pinned BendTT source hash mismatch');
  const source = deriveKernel(original.toString('utf8'));
  const sourceSha256 = sha256(source);
  const directory = path.join(root, '.tools/build/verifier-' + sourceSha256);
  return { directory, source, sourceSha256, originalSourceSha256: sha256(original),
    generatorSha256: sha256(fs.readFileSync(new URL('./derive.mjs', import.meta.url))),
    leanVersion: LEAN_VERSION, kernelPath: path.join(directory, 'bendtt-budget'),
    manifestPath: path.join(directory, 'manifest.json') };
}

/** Explicit, offline installation step, never invoked by a submitted program. */
export function buildVerifier(options = {}) {
  const info = derivedInfo(options.sourceDir);
  const leanHome = path.join(os.homedir(), '.elan/toolchains/leanprover--lean4---v' + LEAN_VERSION, 'bin');
  const lean = options.lean ?? path.join(leanHome, 'lean');
  const leanc = options.leanc ?? path.join(leanHome, 'leanc');
  const run = (bin, args, output) => {
    const log = fs.openSync(output, 'w');
    let got;
    try { got = child.spawnSync(bin, args, { cwd: info.directory, stdio: ['ignore', log, log] }); }
    finally { fs.closeSync(log); }
    if (got.status !== 0 || got.error || got.signal) throw new Error('Verifier build failed: ' + fs.readFileSync(output, 'utf8'));
    return fs.readFileSync(output, 'utf8');
  };
  fs.mkdirSync(info.directory, { recursive: true });
  const version = child.spawnSync(lean, ['--version'], { encoding: 'utf8' });
  if (version.status !== 0 || !version.stdout.startsWith('Lean (version ' + LEAN_VERSION + ',')) throw new Error('Lean ' + LEAN_VERSION + ' required');
  fs.writeFileSync(path.join(info.directory, 'bendtt.lean'), info.source);
  const proofLog = run(lean, ['-c', 'bendtt.c', 'bendtt.lean'], path.join(info.directory, 'lean.log'));
  if (/\bsorryAx\b|\bdeclaration uses .sorry.\b/.test(proofLog)) throw new Error('Unproved verifier theorem');
  const generatedC = fs.readFileSync(path.join(info.directory, 'bendtt.c'), 'utf8');
  const linkedC = useGrowingMainStack(generatedC);
  fs.writeFileSync(path.join(info.directory, 'bendtt-main.c'), linkedC);
  run(leanc, ['-O3', '-DNDEBUG', 'bendtt-main.c', '-Wl,--wrap=initialize_libuv', '-o', 'bendtt-budget'], path.join(info.directory, 'leanc.log'));
  const manifest = { format: 'jaydb-bendtt-budget-v1', originalSourceSha256: info.originalSourceSha256,
    sourceSha256: info.sourceSha256, generatorSha256: info.generatorSha256, leanVersion: LEAN_VERSION,
    leanSha256: sha256(fs.readFileSync(lean)), leancSha256: sha256(fs.readFileSync(leanc)),
    generatedCSha256: sha256(generatedC), linkedCSha256: sha256(linkedC),
    mainAdapterSha256: sha256(fs.readFileSync(new URL('./main.mjs', import.meta.url))),
    kernelSha256: sha256(fs.readFileSync(info.kernelPath)), proofLogSha256: sha256(proofLog),
    proofLog, acceptance: 'Book.checkBudget AND Book.check; generic book_check/consistent/adequate',
    builderSha256: sha256(fs.readFileSync(fileURLToPath(import.meta.url))) };
  fs.writeFileSync(info.manifestPath, JSON.stringify(manifest, null, 2) + '\n');
  return { ...info, source: undefined, ...manifest };
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  try {
    const result = buildVerifier();
    if (process.argv.includes('--write-lock')) fs.copyFileSync(result.manifestPath, new URL('./verifier.lock.json', import.meta.url));
    console.log(JSON.stringify(result, null, 2));
  }
  catch (e) { console.error(e.stack); process.exitCode = 1; }
}
