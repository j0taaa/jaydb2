// Test-only process fault injection, loaded by NODE_OPTIONS in a child service.
// It runs only in the one-off worker compiler, never initialization/pure checks.
import fs from 'node:fs';
import child from 'node:child_process';
import { syncBuiltinESMExports } from 'node:module';
if (process.argv[1]?.endsWith('/tools/service/compile.mjs')) {
  const manifest = JSON.parse(fs.readFileSync(process.argv[2], 'utf8'));
  if (manifest.nativeOptimization && manifest.certificateMode) {
    const spawn = child.spawn;
    child.spawn = function (bin, args, options) {
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
