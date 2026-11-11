#!/usr/bin/env node
// Check and emit the exact private Book with the unmodified official compiler.
import fs from 'node:fs';
import path from 'node:path';
import { spawn } from 'node:child_process';
import { admitSubmission, admitKernel, compileSubmission, compileKernel, emitC, configurationLimits, preflight } from '../admission/index.mjs';
import { sha256 } from '../admission/bootstrap.mjs';

const [manifestFile, outputFile, sourceDir, kernelPath, pureManifestFile] = process.argv.slice(2);
let pureAccepted = false;
const provisionalFiles = [];
function write(file, bytes) {
  fs.writeFileSync(file, bytes, { flag: 'wx', mode: 0o600 });
  provisionalFiles.push(file);
}
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
  let admitted, native;
  const build = async c => {
    write(outputFile, c);
    const original = Buffer.from(c), compiler = '/usr/bin/clang-19';
    const executable = path.join(path.dirname(outputFile), sha256(original) + '.program');
    // A request directory is private; still refuse to replace an existing file.
    if (fs.existsSync(executable)) throw new Error('Native artifact already exists');
    provisionalFiles.push(executable);
    const flags = ['-std=gnu11', manifest.nativeOptimization, '-w', '--no-default-config', outputFile, '-o', executable, '-lm', '-pthread'];
    const started = process.env.JAYDB_BENCH_TIMING ? process.hrtime.bigint() : null;
    const result = await new Promise(resolve => {
      const compilerChild = spawn(compiler, flags, { stdio: ['ignore', 2, 2] });
      let error;
      compilerChild.once('error', cause => { error = cause; });
      compilerChild.once('close', (status, signal) => resolve({ error, status, signal }));
    });
    if (started !== null) try { process.stderr.write('JAYDB_BENCH ' + JSON.stringify({phase: 'c_compilation', ns: String(process.hrtime.bigint() - started)}) + '\n'); } catch {}
    if (result.error || result.signal || result.status !== 0)
      throw new Error('clang-19: ' + (result.error?.message ?? result.signal ?? result.status));
    if (!fs.readFileSync(outputFile).equals(original)) throw new Error('Checked C changed during compilation');
    return { executable, report: { format: 'jaydb-official-c-v1', sourceSha256: sha256(original),
      executableSha256: sha256(fs.readFileSync(executable)), compiler, compilerSha256: sha256(fs.readFileSync(compiler)), flags } };
  };
  if (manifest.nativeOptimization !== undefined && !['-O0', '-O2'].includes(manifest.nativeOptimization))
    throw new Error('Invalid native optimization level');
  try {
    if (manifest.nativeOptimization) {
      const built = await (manifest.purpose ? compileKernel : compileSubmission)({ ...manifest, toolchain }, build);
      admitted = built.admitted; native = built.artifact;
    } else admitted = await (manifest.purpose ? admitKernel : admitSubmission)({ ...manifest, toolchain });
  } catch (workerError) {
    if (workerError.phase === 'compile') {
      // Both checkers accepted every pure declaration. Preserve the build error
      // without risking a redundant pure check's infrastructure failure.
      pureAccepted = Boolean(pure);
    } else if (pure) {
      // A failed worker check needs pure admission to distinguish a rejected
      // client certificate from a host-wrapper failure.
      await (pure.purpose ? admitKernel : admitSubmission)({ ...pure, toolchain });
      pureAccepted = true;
    }
    throw workerError;
  }
  pureAccepted = Boolean(pure);
  let c;
  if (native) {
    // The builder's C bytes were emitted from the sealed Book. No successful
    // report or native receipt exists until both official checkers accepted.
    c = fs.readFileSync(outputFile);
    if (sha256(c) !== native.report.sourceSha256 || sha256(fs.readFileSync(native.executable)) !== native.report.executableSha256)
      throw new Error('Provisional artifact changed before admission completed');
    write(native.executable + '.json', JSON.stringify(native.report));
  } else {
    const started = process.env.JAYDB_BENCH_TIMING ? process.hrtime.bigint() : null;
    c = emitC(admitted);
    if (started !== null) try { process.stderr.write('JAYDB_BENCH ' + JSON.stringify({phase: 'c_emission', ns: String(process.hrtime.bigint() - started)}) + '\n'); } catch {}
    write(outputFile, c);
  }
  write(outputFile + '.json', JSON.stringify({ cSha256: sha256(c),
    backend: 'official-bend-c', admission: admitted.report,
    limits: configurationLimits(admitted) }));
} catch (e) {
  // On every reported failure, admission has awaited the checking/build paths.
  // Discard provisional output before writing the error; hard kills can bypass this.
  for (const file of provisionalFiles.reverse()) fs.rmSync(file, { force: true });
  fs.writeFileSync(outputFile + '.error.json', JSON.stringify({
    code: e.phase === 'compile' ? 'HELPER' : pureAccepted ? 'HOST_COMPILE' : e.code ?? 'HOST_COMPILE',
    phase: e.phase ?? 'host', message: pureAccepted && e.code ? `${e.code}: ${e.message}` : e.message }));
  process.exitCode = 2;
}
