import fs from 'node:fs';
import path from 'node:path';
import { createHash } from 'node:crypto';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { registerHooks, stripTypeScriptTypes } from 'node:module';
import { validateVerifier, verifierInfo } from '../verifier/check.mjs';

export const sha256 = bytes => createHash('sha256').update(bytes).digest('hex');
export const toolchainLock = Object.freeze(JSON.parse(fs.readFileSync(new URL('./toolchain.lock.json', import.meta.url), 'utf8')));

export class AdmissionError extends Error {
  constructor(code, phase, message, options) {
    super(message, options);
    this.name = 'AdmissionError';
    this.code = code;
    this.phase = phase;
  }
}

export function bootstrapInfo(options = {}) {
  const verifier = verifierInfo(options);
  return {
    ...toolchainLock,
    sourceDir: path.resolve(options.sourceDir ?? process.env.JAYDB_BEND_SOURCE ?? fileURLToPath(new URL(`../../.tools/bend-source-${toolchainLock.version}`, import.meta.url))),
    kernelPath: verifier.kernelPath,
    verifier,
  };
}

/** Load the pinned, unmodified official APIs. Node only erases TypeScript. */
export async function loadToolchain(options = {}) {
  const info = bootstrapInfo(options);
  try {
    info.sourceDir = fs.realpathSync(info.sourceDir);
    info.kernelPath = fs.realpathSync(info.kernelPath);
    for (const [file, expected] of Object.entries(info.files)) {
      if (sha256(fs.readFileSync(path.join(info.sourceDir, file))) !== expected) throw new Error(`hash divergente: ${file}`);
    }
    info.verifier = validateVerifier({ kernelPath: info.kernelPath });
    const urls = new Map(['bend.ts', 'safe.ts', 'comp.ts'].map(file =>
      [pathToFileURL(path.join(info.sourceDir, 'bend2', file)).href, info.files['bend2/' + file]]));
    const hook = registerHooks({ load(url, context, nextLoad) {
      if (!urls.has(url)) return nextLoad(url, context);
      const bytes = fs.readFileSync(fileURLToPath(url));
      if (sha256(bytes) !== urls.get(url)) throw new Error(`hash divergente durante import: ${url}`);
      // Transform mode supports safe.ts's TypeScript parameter property.
      // No source replacement, instrumentation or compiler adaptation occurs.
      return { format: 'module', source: stripTypeScriptTypes(bytes.toString('utf8'), { mode: 'transform' }), shortCircuit: true };
    } });
    try {
      const B = await import(pathToFileURL(path.join(info.sourceDir, 'bend2/bend.ts')).href);
      const S = await import(pathToFileURL(path.join(info.sourceDir, 'bend2/safe.ts')).href);
      const C = await import(pathToFileURL(path.join(info.sourceDir, 'bend2/comp.ts')).href);
      return { B, S, C, info };
    } finally { hook.deregister(); }
  } catch (cause) {
    throw new AdmissionError('TOOLCHAIN', 'bootstrap', `Toolchain oficial indisponível: ${cause.message}`, { cause });
  }
}
