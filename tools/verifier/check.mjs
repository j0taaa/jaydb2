import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import child from 'node:child_process';
import { createHash } from 'node:crypto';
import { fileURLToPath } from 'node:url';

const pin = JSON.parse(fs.readFileSync(new URL('../admission/toolchain.lock.json', import.meta.url), 'utf8'));
const sha256 = bytes => createHash('sha256').update(bytes).digest('hex');
export class VerifierInfrastructure extends Error {}

export function verifierInfo(options = {}) {
  return { kernelPath: path.resolve(options.kernelPath ?? process.env.JAYDB_BENDTT ?? fileURLToPath(new URL(`../../.tools/bendtt-${pin.kernelSha256}`, import.meta.url))),
    kernelSha256: pin.kernelSha256 };
}

export function validateVerifier(options = {}) {
  const info = verifierInfo(options);
  if (sha256(fs.readFileSync(info.kernelPath)) !== info.kernelSha256) throw new Error('Official BendTT binary hash mismatch');
  fs.accessSync(info.kernelPath, fs.constants.X_OK);
  return Object.freeze(info);
}

/** Run the official BendTT executable with its original CLI and defaults. */
export function checkKernelFile(input, info) {
  if (info.kernelSha256 !== pin.kernelSha256 || sha256(fs.readFileSync(info.kernelPath)) !== pin.kernelSha256) throw new VerifierInfrastructure('Official BendTT binary hash mismatch');
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), 'jaydb-verifier-log-'));
  const log = path.join(directory, 'out');
  try {
    const fd = fs.openSync(log, 'w', 0o600);
    let got;
    try { got = child.spawnSync(info.kernelPath, [input], { stdio: ['ignore', fd, fd] }); }
    finally { fs.closeSync(fd); }
    const out = fs.readFileSync(log, 'utf8').trim();
    if (got.error || got.signal || got.status === null) throw new VerifierInfrastructure(got.error?.message ?? 'Verifier terminated by ' + got.signal);
    if (got.status === 0 && out === 'ALL PROOFS CHECK') return { why: null };
    if (got.status === 1 && out.startsWith('SOME PROOFS FAIL\n')) {
      const why = out.slice('SOME PROOFS FAIL\n'.length);
      // Book.check prefixes the original checker's exhaustion with its def.
      // A stopped check establishes no mathematical rejection of the proof.
      if (/^(?:In [^\r\n]+:\n)?out of fuel$/.test(why)) throw new VerifierInfrastructure(why);
      return { why };
    }
    throw new VerifierInfrastructure(out || 'Verifier exited without a verdict: ' + got.status);
  } finally { fs.rmSync(directory, { recursive: true, force: true }); }
}

/** The official translator serializes the same Book checked by Bend. */
export function checkBook(S, book, info) {
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), 'jaydb-verifier-'));
  try {
    const input = path.join(directory, 'in.bendtt');
    const oos = S.safe_emit(book, input);
    const inputSha256 = sha256(fs.readFileSync(input));
    if (oos.length) throw new VerifierInfrastructure('Official BendTT representation out of scope:\n' + oos.join(''));
    return { ...checkKernelFile(input, info), inputSha256 };
  } finally { fs.rmSync(directory, { recursive: true, force: true }); }
}
