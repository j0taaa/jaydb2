import fs from 'node:fs';
import path from 'node:path';
import { createHash } from 'node:crypto';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { registerHooks } from 'node:module';
import { loadFrontendCache } from './frontend-cache.mjs';
import { verifierInfo, validateVerifier } from '../verifier/check.mjs';

export const sha256 = (bytes) => createHash('sha256').update(bytes).digest('hex');
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
  const info = {
    version: toolchainLock.version,
    sourceDir: path.resolve(options.sourceDir ?? process.env.JAYDB_BEND_SOURCE ?? fileURLToPath(new URL(`../../.tools/bend-source-${toolchainLock.version}`, import.meta.url))),
    kernelPath: path.resolve(options.kernelPath ?? process.env.JAYDB_BENDTT ?? fileURLToPath(new URL(`../../.tools/bendtt-${toolchainLock.kernelSha256}`, import.meta.url))),
    sourceUrl: toolchainLock.sourceUrl,
    archiveSha256: toolchainLock.archiveSha256,
    files: toolchainLock.files,
    kernelSha256: toolchainLock.kernelSha256,
    officialBinarySha256: toolchainLock.officialBinarySha256,
    frontendObserverSha256: sha256(fs.readFileSync(new URL('./frontend-observer.mjs', import.meta.url))),
    conversionSha256: sha256(fs.readFileSync(new URL('./conversion.mjs', import.meta.url))),
    safeNumeralsSha256: sha256(fs.readFileSync(new URL('./safe-numerals.mjs', import.meta.url))),
    safeStringsSha256: sha256(fs.readFileSync(new URL('./safe-strings.mjs', import.meta.url))),
    safeTemplatesSha256: sha256(fs.readFileSync(new URL('./safe-templates.mjs', import.meta.url))),
    frontendResourcesSha256: sha256(fs.readFileSync(new URL('./frontend-resources.mjs', import.meta.url))),
    verifierRunnerSha256: sha256(fs.readFileSync(new URL('../verifier/check.mjs', import.meta.url))),
    frontend: JSON.parse(fs.readFileSync(new URL('./frontend.lock.json', import.meta.url))),
  };
  info.verifier = verifierInfo(info.sourceDir, options.verifier);
  return info;
}

// Bootstrap is deliberately offline. In particular safe_check must never fall
// back to building a kernel selected by PATH, HOME, or the request's environment.
export async function loadToolchain(options = {}) {
  const info = bootstrapInfo(options);
  try {
    info.sourceDir = fs.realpathSync(info.sourceDir);
    info.kernelPath = fs.realpathSync(info.kernelPath);
    for (const [file, expected] of Object.entries(info.files)) {
      if (sha256(fs.readFileSync(path.join(info.sourceDir, file))) !== expected) {
        throw new Error(`hash divergente: ${file}`);
      }
    }
    if (sha256(fs.readFileSync(info.kernelPath)) !== info.kernelSha256) {
      throw new Error('hash divergente: BendTT');
    }
    fs.accessSync(info.kernelPath, fs.constants.X_OK);
    info.verifier = validateVerifier(info.sourceDir, options.verifier);
    const frontend = loadFrontendCache();
    if (JSON.stringify(frontend.pin.originalFiles) !== JSON.stringify(info.files)) throw new Error('Frontend original source pin mismatch');
    // safe.ts has a TS parameter property. Node's default strip-only loader
    // cannot read it; use Node's own transformer, confined to the pinned files.
    const urls = new Map(['bend.ts', 'safe.ts', 'comp.ts'].map(f => [pathToFileURL(path.join(info.sourceDir, 'bend2', f)).href, info.files['bend2/' + f]]));
    const hook = registerHooks({ resolve(specifier, context, nextResolve) {
      if (specifier === 'jaydb:admission-closure') return { url: new URL('./closed-instances.mjs', import.meta.url).href, shortCircuit: true };
      return nextResolve(specifier, context);
    }, load(url, context, nextLoad) {
      if (!urls.has(url)) return nextLoad(url, context);
      const bytes = fs.readFileSync(fileURLToPath(url));
      if (sha256(bytes) !== urls.get(url)) throw new Error(`hash divergente durante import: ${url}`);
      const name = path.basename(fileURLToPath(url), '.ts');
      return { format: 'module', source: frontend.sources[name], shortCircuit: true };
    } });
    try {
      const B = await import(pathToFileURL(path.join(info.sourceDir, 'bend2/bend.ts')).href);
      const S = await import(pathToFileURL(path.join(info.sourceDir, 'bend2/safe.ts')).href);
      const C = await import(pathToFileURL(path.join(info.sourceDir, 'bend2/comp.ts')).href);
      return { B, S, C, info };
    } finally { hook.deregister(); }
  } catch (cause) {
    throw new AdmissionError('TOOLCHAIN', 'bootstrap', `Toolchain fixada indisponível: ${cause.message}`, { cause });
  }
}
