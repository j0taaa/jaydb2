#!/usr/bin/env node
// Check and emit the exact private Book with the unmodified official compiler.
import fs from 'node:fs';
import { admitSubmission, admitKernel, emitC, configurationLimits } from '../admission/index.mjs';
import { sha256 } from '../admission/bootstrap.mjs';

const [manifestFile, outputFile, sourceDir, kernelPath, pureManifestFile] = process.argv.slice(2);
try {
  const manifest = JSON.parse(fs.readFileSync(manifestFile, 'utf8'));
  const toolchain = { sourceDir, kernelPath };
  if (pureManifestFile) {
    const pure = JSON.parse(fs.readFileSync(pureManifestFile, 'utf8'));
    if (pure.certificateMode !== manifest.certificateMode) throw new Error('Pure and executable certificate modes differ');
    const fullHashes = new Map(manifest.dependencies.map(d => [d.path, d.sha256]));
    for (const dependency of pure.dependencies) if (dependency.path !== pure.entry && fullHashes.get(dependency.path) !== dependency.sha256)
      throw new Error('Pure and executable sources differ');
    await (pure.purpose ? admitKernel : admitSubmission)({ ...pure, toolchain });
  }
  const admitted = await (manifest.purpose ? admitKernel : admitSubmission)({ ...manifest, toolchain });
  const c = emitC(admitted);
  fs.writeFileSync(outputFile, c, { flag: 'wx', mode: 0o600 });
  fs.writeFileSync(outputFile + '.json', JSON.stringify({ cSha256: sha256(c),
    backend: 'official-bend-c', admission: admitted.report,
    limits: configurationLimits(admitted) }), { flag: 'wx', mode: 0o600 });
} catch (e) {
  fs.writeFileSync(outputFile + '.error.json', JSON.stringify({ code: e.code ?? 'HOST_COMPILE', phase: e.phase ?? 'host', message: e.message }));
  process.exitCode = 2;
}
