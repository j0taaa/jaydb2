#!/usr/bin/env node
// Check and emit the exact private Book with the unmodified official compiler.
import fs from 'node:fs';
import path from 'node:path';
import { spawn, spawnSync } from 'node:child_process';
import { admitSubmission, admitKernel, compileSubmission, compileKernel, emitC, configurationLimits, preflight } from '../admission/index.mjs';
import { sha256 } from '../admission/bootstrap.mjs';

const [manifestFile, outputFile, sourceDir, kernelPath, pureManifestFile, gpuOption = '0'] = process.argv.slice(2);
let pureAccepted = false;
// Record (not pin) the environment's CUDA libraries in the trusted base: the
// dynamic loader resolves them at each run; this is provenance, not attestation.
function resolvedCudaLibraries(executable) {
  const listed = spawnSync('/usr/bin/ldd', [executable], { encoding: 'utf8', env: process.env });
  if (listed.error || listed.status !== 0) throw new Error('GPU_BUILD: ldd failed');
  const libraries = {};
  for (const [, name, file] of listed.stdout.matchAll(/^\s*(lib(?:cuda|nvrtc)\S*) => (\/\S+)/gm))
    libraries[name] = { path: fs.realpathSync(file), sha256: sha256(fs.readFileSync(file)) };
  if (!Object.keys(libraries).some(n => n.startsWith('libcuda.')) || !Object.keys(libraries).some(n => n.startsWith('libnvrtc.')))
    throw new Error('GPU_BUILD: cannot resolve libcuda/libnvrtc');
  return libraries;
}
const provisionalFiles = [];
function write(file, bytes) {
  fs.writeFileSync(file, bytes, { flag: 'wx', mode: 0o600 });
  provisionalFiles.push(file);
}
try {
  const gpuMiB = /^(0|[1-9][0-9]{0,3})$/.test(gpuOption) ? Number(gpuOption) : NaN;
  if (gpuMiB !== 0 && !(gpuMiB >= 64 && gpuMiB <= 4096)) throw new Error('Invalid GPU MiB');
  const cuda = gpuMiB !== 0;
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
    if (cuda) flags.push('-DBEND_CUDA=1', '-lcuda', '-lnvrtc');
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
    let gpuSha256, cudaLibraries;
    if (cuda) {
      const device = executable + '.gpu';
      // --gpu-build can exit zero without writing; never adopt a stale file.
      if (fs.existsSync(device)) throw new Error('GPU artifact already exists');
      provisionalFiles.push(device);
      const prebuild = await new Promise(resolve => {
        const child = spawn(executable, ['+RTS', '--gpu-build', '-RTS'], {
          env: { ...process.env, BENDRTS: '' }, stdio: ['ignore', 'ignore', 'pipe'] });
        let error, stderr = '';
        child.stderr.on('data', bytes => { if (stderr.length < 65536) stderr += bytes; });
        child.once('error', cause => { error = cause; });
        child.once('close', (status, signal) => resolve({ error, stderr, status, signal }));
      });
      // Official --gpu-build can exit zero without a device. Require a cubin.
      if (prebuild.error || prebuild.signal || prebuild.status !== 0 || !fs.existsSync(device)
          || !fs.lstatSync(device).isFile() || fs.statSync(device).size <= 8)
        throw new Error('GPU_BUILD: GPU prebuild failed: ' + (prebuild.stderr.slice(0, 65536) || prebuild.error?.message || 'no artifact'));
      gpuSha256 = sha256(fs.readFileSync(device));
      cudaLibraries = resolvedCudaLibraries(executable);
    }
    return { executable, report: { format: 'jaydb-official-c-v1', sourceSha256: sha256(original),
      executableSha256: sha256(fs.readFileSync(executable)), compiler, compilerSha256: sha256(fs.readFileSync(compiler)), flags,
      backend: cuda ? 'cuda' : 'cpu',
      ...(cuda ? { gpuSha256, gpuMiB, cudaLibraries, hasBangs: /^#define\s+BANGS\s+[1-9]/m.test(original.toString()) } : {}) } };
  };
  if (manifest.nativeOptimization !== undefined && !['-O0', '-O2'].includes(manifest.nativeOptimization))
    throw new Error('Invalid native optimization level');
  try {
    if (cuda) {
      // CUDA is never entered before BOTH official checkers accept the sealed
      // Book. Keep the default CPU concurrent-check/build pipeline unchanged.
      if (!manifest.nativeOptimization) throw new Error('CUDA requires a native optimization level');
      admitted = await (manifest.purpose ? admitKernel : admitSubmission)({ ...manifest, toolchain });
      // Both checkers accepted: a build/prebuild failure is a compile-phase
      // error, as on the CPU path, with no redundant pure re-check.
      native = await build(emitC(admitted)).catch(e => { throw Object.assign(e, { phase: 'compile' }); });
    } else if (manifest.nativeOptimization) {
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
    if (sha256(c) !== native.report.sourceSha256 || sha256(fs.readFileSync(native.executable)) !== native.report.executableSha256
        || (cuda && sha256(fs.readFileSync(native.executable + '.gpu')) !== native.report.gpuSha256))
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
