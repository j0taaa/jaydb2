#!/usr/bin/env node
// Helper only: this process verifies/emits; it never executes client programs.
import fs from 'node:fs';
import { fileURLToPath } from 'node:url';
import { admitSubmission, admitKernel, emitGenericC, configurationLimits } from '../admission/index.mjs';
import { sha256 } from '../admission/bootstrap.mjs';

const [manifestFile, outputFile, sourceDir, kernelPath] = process.argv.slice(2);
try {
  const manifest = JSON.parse(fs.readFileSync(manifestFile, 'utf8'));
  const toolchain = { sourceDir, kernelPath, verifier: {
    kernelPath: fileURLToPath(new URL('../verifier/installed/bendtt-budget', import.meta.url)),
    manifestPath: fileURLToPath(new URL('../verifier/installed/manifest.json', import.meta.url)),
  } };
  const admitted = await (manifest.purpose ? admitKernel : admitSubmission)({ ...manifest, toolchain });
  const backendSha256 = sha256(fs.readFileSync(new URL('../native/generic.mjs', import.meta.url)));
  const emitted = await emitGenericC(admitted, { backendSha256 });
  fs.writeFileSync(outputFile, emitted.c, { flag: 'wx', mode: 0o600 });
  const limits = configurationLimits(admitted);
  fs.writeFileSync(outputFile + '.json', JSON.stringify({ ...emitted, c: undefined, admission: admitted.report, limits }), { flag: 'wx', mode: 0o600 });
} catch (e) {
  fs.writeFileSync(outputFile + '.error.json', JSON.stringify({ code: e.code ?? 'HOST_COMPILE', phase: e.phase ?? 'host', message: e.message }));
  process.exitCode = 2;
}
