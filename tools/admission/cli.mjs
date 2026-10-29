#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { parseArgs } from 'node:util';
import { admitSubmission, admitKernel, emitC, emitGenericC, bootstrapInfo, AdmissionError } from './index.mjs';

try {
  const { values } = parseArgs({ options: {
    manifest: { type: 'string' }, 'emit-c': { type: 'string' },
    'source-dir': { type: 'string' }, kernel: { type: 'string' },
    'generic-backend-sha256': { type: 'string' },
    bootstrap: { type: 'boolean' }, help: { type: 'boolean' },
  } });
  const toolchain = { sourceDir: values['source-dir'], kernelPath: values.kernel };
  if (values.help) {
    console.log('node tools/admission/cli.mjs --manifest HOST.json [--emit-c out.c] [--generic-backend-sha256 SHA] [--source-dir DIR] [--kernel BIN]\nnode tools/admission/cli.mjs --bootstrap');
  } else if (values.bootstrap) {
    console.log(JSON.stringify(bootstrapInfo(toolchain), null, 2));
  } else {
    if (!values.manifest) throw new Error('--manifest HOST.json exigido');
    const manifestPath = path.resolve(values.manifest);
    const manifest = JSON.parse(fs.readFileSync(manifestPath, 'utf8'));
    // A manifest path is host configuration; relative source directories resolve
    // against it, never against a process cwd or a Bend import's directory.
    manifest.submissionDir = path.resolve(path.dirname(manifestPath), manifest.submissionDir);
    const result = await (manifest.purpose ? admitKernel : admitSubmission)({ ...manifest, toolchain });
    if (values['emit-c']) {
      const c = values['generic-backend-sha256'] ? (await emitGenericC(result, { backendSha256: values['generic-backend-sha256'] })).c : emitC(result);
      fs.writeFileSync(values['emit-c'], c, { flag: 'wx' });
    }
    console.log(JSON.stringify(result.report, null, 2));
  }
} catch (error) {
  console.error(JSON.stringify({ code: error.code ?? 'CLI', phase: error.phase ?? 'cli', message: error.message }));
  process.exitCode = error instanceof AdmissionError && !['TOOLCHAIN', 'SOURCE_IO', 'FRONTEND_INFRASTRUCTURE', 'BENDTT_INFRASTRUCTURE', 'COMPILE', 'BACKEND', 'BACKEND_CHANGED', 'BOOK_CHANGED'].includes(error.code) ? 2 : 3;
}
