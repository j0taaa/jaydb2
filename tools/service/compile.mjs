#!/usr/bin/env node
// Check and emit the exact private Book with the unmodified official compiler.
import fs from 'node:fs';
import { admitSubmission, admitKernel, emitC, configurationLimits, preflight } from '../admission/index.mjs';
import { sha256 } from '../admission/bootstrap.mjs';

const [manifestFile, outputFile, sourceDir, kernelPath, pureManifestFile] = process.argv.slice(2);
let pureAccepted = false;
try {
  const manifest = JSON.parse(fs.readFileSync(manifestFile, 'utf8'));
  const toolchain = { sourceDir, kernelPath };
  let pure;
  if (pureManifestFile) {
    pure = JSON.parse(fs.readFileSync(pureManifestFile, 'utf8'));
    if (pure.certificateMode !== manifest.certificateMode) throw new Error('Pure and executable certificate modes differ');
    const fullHashes = new Map(manifest.dependencies.map(d => [d.path, d.sha256]));
    const fullRecords = new Map(manifest.dependencies.map(d => [d.path, d]));
    for (const key of ['openTargets', 'canonicalRefs', 'purpose', 'initialization'])
      if (JSON.stringify(pure[key]) !== JSON.stringify(manifest[key])) throw new Error('Pure and executable policies differ: ' + key);
    for (const dependency of pure.dependencies) if (dependency.path !== pure.entry && fullHashes.get(dependency.path) !== dependency.sha256)
      throw new Error('Pure and executable sources differ');
    for (const dependency of pure.dependencies) if (dependency.path !== pure.entry) {
      const full = fullRecords.get(dependency.path);
      if (dependency.role !== full.role || JSON.stringify(dependency.exports) !== JSON.stringify(full.exports))
        throw new Error('Pure and executable source roles differ');
    }
    // The generated pure root contains imports only. Every actual declaration
    // is in the executable Book, which BOTH official checkers check in full.
    // Preflight still snapshots the entire pure graph; the full audit covers its declarations.
    const plan = preflight(pure, Boolean(pure.purpose));
    if (plan.records.get(pure.entry).body.trim() !== '' || plan.records.has(manifest.kernel.module) || plan.records.has(manifest.entry))
      throw new Error('Expected an import-only pure root without the runtime kernel');
  }
  let admitted;
  try {
    admitted = await (manifest.purpose ? admitKernel : admitSubmission)({ ...manifest, toolchain });
  } catch (workerError) {
    // Only a failed worker needs the separate pure check to distinguish a bad
    // client certificate from a host-wrapper/compiler failure. Successful Books
    // already checked the same pure declarations, and need no second proof run.
    if (pure) {
      await (pure.purpose ? admitKernel : admitSubmission)({ ...pure, toolchain });
      pureAccepted = true;
    }
    throw workerError;
  }
  pureAccepted = Boolean(pure);
  const started = process.env.JAYDB_BENCH_TIMING ? process.hrtime.bigint() : null;
  const c = emitC(admitted);
  if (started !== null) try { process.stderr.write('JAYDB_BENCH ' + JSON.stringify({phase: 'c_emission', ns: String(process.hrtime.bigint() - started)}) + '\n'); } catch {}
  fs.writeFileSync(outputFile, c, { flag: 'wx', mode: 0o600 });
  fs.writeFileSync(outputFile + '.json', JSON.stringify({ cSha256: sha256(c),
    backend: 'official-bend-c', admission: admitted.report,
    limits: configurationLimits(admitted) }), { flag: 'wx', mode: 0o600 });
} catch (e) {
  fs.writeFileSync(outputFile + '.error.json', JSON.stringify({
    code: pureAccepted ? 'HOST_COMPILE' : e.code ?? 'HOST_COMPILE',
    phase: e.phase ?? 'host', message: pureAccepted && e.code ? `${e.code}: ${e.message}` : e.message }));
  process.exitCode = 2;
}
