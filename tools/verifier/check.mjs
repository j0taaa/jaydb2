import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import child from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { derivedInfo } from './build.mjs';
import { sha256 } from './derive.mjs';

export class VerifierInfrastructure extends Error {}

export function verifierInfo(sourceDir, options = {}) {
  const info = derivedInfo(sourceDir);
  const pin = JSON.parse(fs.readFileSync(new URL('./verifier.lock.json', import.meta.url), 'utf8'));
  return { ...pin, kernelPath: path.resolve(options.kernelPath ?? info.kernelPath),
    manifestPath: path.resolve(options.manifestPath ?? info.manifestPath) };
}

export function validateVerifier(sourceDir, options = {}) {
  const derived = derivedInfo(sourceDir);
  const info = verifierInfo(sourceDir, options);
  for (const field of ['sourceSha256', 'originalSourceSha256', 'generatorSha256', 'leanVersion']) {
    if (info[field] !== derived[field]) throw new Error('Verifier derivation pin mismatch: ' + field);
  }
  for (const [field, file] of [['mainAdapterSha256', './main.mjs'], ['builderSha256', './build.mjs']]) {
    if (info[field] !== sha256(fs.readFileSync(new URL(file, import.meta.url)))) throw new Error('Verifier implementation pin mismatch: ' + field);
  }
  const installed = JSON.parse(fs.readFileSync(info.manifestPath, 'utf8'));
  for (const [key, expected] of Object.entries(info)) {
    if (key !== 'kernelPath' && key !== 'manifestPath' && JSON.stringify(installed[key]) !== JSON.stringify(expected)) throw new Error('Verifier installation manifest mismatch: ' + key);
  }
  if (sha256(fs.readFileSync(info.kernelPath)) !== info.kernelSha256) throw new Error('Verifier binary hash mismatch');
  fs.accessSync(info.kernelPath, fs.constants.X_OK);
  return Object.freeze(info);
}

function fuelValue(n) {
  if (typeof n !== 'bigint' && (typeof n !== 'string' || !/^[1-9][0-9]*$/.test(n))) throw new VerifierInfrastructure('initialFuel must be an exact positive decimal integer');
  const value = BigInt(n);
  if (value <= 0n) throw new VerifierInfrastructure('initialFuel must be positive');
  return value;
}

function modelBudget(n) {
  try { return fuelValue(n); }
  catch { throw new VerifierInfrastructure('initialModelFuel must be an exact positive decimal integer'); }
}

/** Retry the same immutable input with increasing fuel; no maximum. */
export function checkKernelFile(input, info, options = {}) {
  let fuel = fuelValue(options.initialFuel ?? '400000000');
  let attempts = 0n;
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), 'jaydb-verifier-log-'));
  const log = path.join(directory, 'out');
  try {
    for (;;) {
      if (sha256(fs.readFileSync(info.kernelPath)) !== info.kernelSha256) throw new VerifierInfrastructure('Verifier changed during admission');
      const fd = fs.openSync(log, 'w', 0o600);
      let got;
      try {
        const env = { ...process.env };
        delete env.LEAN_STACK_SIZE_KB;
        // The hashed main adapter runs synchronously on the growing OS stack.
        // These variables additionally prevent inherited worker settings.
        env.LEAN_NUM_THREADS = '0';
        env.LEAN_MAIN_USE_THREAD = '0';
        got = child.spawnSync(info.kernelPath, [input, fuel.toString()], { env,
          stdio: ['ignore', fd, fd] });
      } finally { fs.closeSync(fd); }
      attempts++;
      const out = fs.readFileSync(log, 'utf8').trim();
      if (got.error || got.signal || got.status === null) throw new VerifierInfrastructure(got.error?.message ?? 'Verifier terminated by ' + got.signal);
      if (got.status === 75 && out === 'BENDTT BUDGET EXHAUSTED') { fuel *= 2n; continue; }
      if (got.status === 0 && out === 'ALL PROOFS CHECK') return { why: null, fuel: fuel.toString(), attempts: attempts.toString() };
      if (got.status === 1 && out.startsWith('SOME PROOFS FAIL\n')) {
        return { why: out.slice('SOME PROOFS FAIL\n'.length), fuel: fuel.toString(), attempts: attempts.toString() };
      }
      throw new VerifierInfrastructure(out || 'Verifier exited without a verdict: ' + got.status);
    }
  } finally { fs.rmSync(directory, { recursive: true, force: true }); }
}

/** Serialize once from the very Book checked by the primary checker. */
export function checkBook(S, book, info, options = {}) {
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), 'jaydb-verifier-'));
  try {
    const input = path.join(directory, 'in.bendtt');
    if (typeof S.admission_safe_emit !== 'function') throw new VerifierInfrastructure('Pinned Safe stage adapter is unavailable');
    const budget = modelBudget(options.initialModelFuel ?? '4194304');
    const emitted = S.admission_safe_emit(book, input, { modelFuel: budget.toString(), actualTargets: options.actualTargets });
    const model = { modelFuel: emitted.modelFuel, modelAttempts: emitted.modelAttempts,
      schemas: emitted.schemas, instances: emitted.instances,
      ...(emitted.correspondence ? { correspondence: emitted.correspondence } : {}) };
    if (emitted.oos.length) throw new VerifierInfrastructure('BendTT representation unsupported:\n' + emitted.oos.join(''));
    return { ...checkKernelFile(input, info, options), ...model, inputSha256: sha256(fs.readFileSync(input)) };
  } finally { fs.rmSync(directory, { recursive: true, force: true }); }
}
