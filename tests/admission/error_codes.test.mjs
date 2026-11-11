import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';

const root = new URL('../../', import.meta.url);
const contract = fs.readFileSync(new URL('contract/HostErrors.bend', root), 'utf8');
const table = contract.match(/def certificate_codes\(\)[\s\S]*?\n  (\[[^\n]+\])/);
assert.ok(table, 'find the contract certificate_codes() literal');
const certificate = new Set(JSON.parse(table[1]));
// Deliberate technical classifications; additions require an explicit review.
// ADT/ORACLE_PROOF/INSTANCE_MATCH also occur as non-error source tokens, but
// if observed as error codes the contract deliberately returns failure.
const failure = new Set([
  'ADT', 'BACKEND', 'BACKEND_CHANGED', 'BENDTT_INFRASTRUCTURE', 'BOOK_CHANGED',
  'CLI', 'COMPILE', 'CONFIGURATION', 'CONTRACT', 'ENOENT', 'FRONTEND_INFRASTRUCTURE',
  'HASH', 'HELPER', 'HOST_COMPILE', 'INITIALIZATION', 'INSTANCE_MATCH',
  'KERNEL_ABI', 'MANIFEST', 'ORACLE_PROOF', 'PATH', 'SOURCE_IO', 'STAGING',
  'TOOLCHAIN', 'USAGE',
]);
// These are source-template placeholders rather than error codes.
const nonCodes = new Set(['FUNCTION', 'PARSER', 'WORKER_ENTRY']);

function checkLiteralCodes(source, file) {
  // Conservatively inventory every uppercase string literal, rather than
  // recognizing only today's throw/fail syntax (which would miss new forms).
  for (const [, code] of source.matchAll(/['"`]([A-Z][A-Z0-9_]+)['"`]/g)) {
    assert.ok(certificate.has(code) || failure.has(code) || nonCodes.has(code),
      `${file}: ${code} needs a deliberate certificate/failure classification`);
  }
}

test('Node admission/service code literals have deliberate contract classifications', () => {
  assert.equal(certificate.size, 17);
  for (const code of failure) assert.ok(!certificate.has(code), `${code} must remain failure`);
  for (const directory of ['tools/admission', 'tools/service']) {
    for (const name of fs.readdirSync(new URL(directory + '/', root), { recursive: true })) {
      if (!name.endsWith('.mjs')) continue;
      const file = path.posix.join(directory, name);
      checkLiteralCodes(fs.readFileSync(new URL(file, root), 'utf8'), file);
    }
  }
});

test('a new literal rejection code fails until deliberately classified', () => {
  assert.throws(() => checkLiteralCodes("reject('NEW_PROOF_REJECTION', 'reason')", 'control'),
    /NEW_PROOF_REJECTION needs a deliberate/);
});
