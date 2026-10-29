#!/usr/bin/env node
// Helper only: this process verifies/emits; it never executes client programs.
import fs from 'node:fs';
import { fileURLToPath } from 'node:url';
import { admitSubmission, admitKernel, emitGenericC } from '../admission/index.mjs';
import { loadToolchain, sha256 } from '../admission/bootstrap.mjs';

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
  const { B } = await loadToolchain(toolchain);
  const book = admitted.book;
  const wnf = t => B.term_wnf(book, t);
  const nat = t => {
    let count = 0n;
    for (;;) {
      // Preserve literal compression before WNF opens it into Succ. These
      // arithmetic heads belong to the hash-pinned Base, not administrator code.
      t = B.term_strip(t);
      if (t.$ === 'Lit' && t.k === 'Nat') {
        if (!Number.isSafeInteger(t.v) || t.v < 0) throw new Error('Inexact Nat in official frontend metadata');
        return count + BigInt(t.v);
      }
      let head = t, args = [];
      while (head.$ === 'App') { args.unshift(head.x); head = B.term_strip(head.f); }
      if (head.$ === 'Ref' && args.length === 2 && ['Nat.add', 'Nat.mul', 'Nat.sub', 'Nat.min', 'Nat.max'].includes(head.k)) {
        const a = nat(args[0]), b = nat(args[1]);
        return count + ({'Nat.add': () => a + b, 'Nat.mul': () => a * b,
          'Nat.sub': () => a > b ? a - b : 0n, 'Nat.min': () => a < b ? a : b,
          'Nat.max': () => a > b ? a : b}[head.k])();
      }
      if (t.$ === 'Ctr' && t.k === 'Zero') return count;
      if (t.$ === 'Ctr' && t.k === 'Succ') { count++; t = t.x[0]; continue; }
      const reduced = wnf(t);
      if (reduced !== t) { t = reduced; continue; }
      throw new Error('Expected closed Nat in configuration');
    }
  };
  const lim = wnf(B.App(B.Ref('Semantica:limites'), B.Ref('Configuration:config')));
  if (lim.$ !== 'Ctr' || lim.k !== 'Semantica:Limites' || lim.x.length !== 3) throw new Error('Invalid configuration limits');
  const names = ['mensagem', 'estado', 'resposta'];
  const limits = Object.fromEntries(names.map((name, i) => [name, String(nat(lim.x[i]))]));
  fs.writeFileSync(outputFile + '.json', JSON.stringify({ ...emitted, c: undefined, admission: admitted.report, limits }), { flag: 'wx', mode: 0o600 });
} catch (e) {
  fs.writeFileSync(outputFile + '.error.json', JSON.stringify({ code: e.code ?? 'HOST_COMPILE', phase: e.phase ?? 'host', message: e.message }));
  process.exitCode = 2;
}
