// Test-only process fault injection, loaded by NODE_OPTIONS in a child service.
// It activates only for worker manifests, leaving startup compiler calls alone.
import fs from 'node:fs';
import child from 'node:child_process';
import { syncBuiltinESMExports } from 'node:module';
if (process.argv[1]?.endsWith('/tools/service/compile.mjs')) {
  const manifest = JSON.parse(fs.readFileSync(process.argv[2], 'utf8'));
  if (manifest.nativeOptimization && manifest.certificateMode) {
    const spawn = child.spawn, spawnSync = child.spawnSync;
    child.spawnSync = function (bin, args, options) {
      if (String(bin).includes('/bendtt-') && process.env.JAYDB_TEST_KERNEL === 'accept-once') {
        fs.writeFileSync(process.env.JAYDB_TEST_COMPILED + '.rechecked', 'unexpected pure recheck');
        return { status: 19 }; // Pure admission uses the synchronous checker.
      }
      return spawnSync(bin, args, options);
    };
    child.spawn = function (bin, args, options) {
      if (bin === '/usr/bin/clang-19' && process.env.JAYDB_TEST_CLANG === 'reject') {
        // Leave a partial binary as a failed compiler may do.
        fs.writeFileSync(args[args.indexOf('-o') + 1], 'partial');
        return spawn(process.execPath, ['-e', 'process.exit(17)'], options);
      }
      if (String(bin).includes('/bendtt-') && process.env.JAYDB_TEST_KERNEL === 'reject') {
        // Refuse only after a real speculative Clang invocation completed.
        return spawn(process.execPath, ['-e', `
          const fs = require('node:fs');
          const timer = setInterval(() => {
            if (fs.existsSync(process.env.JAYDB_TEST_COMPILED)) {
              clearInterval(timer);
              const path = require('node:path');
              const binary = fs.readFileSync(process.env.JAYDB_TEST_COMPILED, 'utf8');
              if (fs.existsSync(binary + '.json') || fs.existsSync(path.join(path.dirname(binary), 'checked.c.json')))
                fs.writeFileSync(process.env.JAYDB_TEST_COMPILED + '.premature', 'receipt before admission');
              console.log('SOME PROOFS FAIL\\nIn injected:\\nexpected: <ok>\\nobserved: .wrong');
              process.exit(1);
            }
          }, 5);
        `], options);
      }
      const processChild = spawn(bin, args, options);
      if (bin === '/usr/bin/clang-19') processChild.once('close', status => {
        if (status !== 0) return;
        const binary = args[args.indexOf('-o') + 1];
        // A positive control proves this sentinel detects an actual launch.
        fs.writeFileSync(binary, '#!/bin/sh\nprintf executed > "' + process.env.JAYDB_TEST_EXECUTED + '"\nexit 99\n', { mode: 0o700 });
        fs.writeFileSync(process.env.JAYDB_TEST_COMPILED, binary);
      });
      return processChild;
    };
    syncBuiltinESMExports();
  }
}
