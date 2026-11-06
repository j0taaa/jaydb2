/** Fake protocol peer only; native database behavior is tested separately. */
import { appendFileSync } from 'node:fs';
import { decode, frame } from '../src/index.ts';
import type { Value } from '../src/index.ts';

if (process.argv[2]) appendFileSync(process.argv[2], 'started\n');
let bytes = Buffer.alloc(0);
let handle: string | undefined;
for await (const chunk of process.stdin) {
  bytes = Buffer.concat([bytes, chunk]);
  while (bytes.length >= 8 && bytes.readBigUInt64BE() <= BigInt(bytes.length - 8)) {
    const length = Number(bytes.readBigUInt64BE());
    const body = bytes.subarray(8, 8 + length); bytes = bytes.subarray(8 + length);
    const op = body[0] === 7 ? body[1] : undefined;
    const request = decode(op === undefined ? body : body.subarray(2)) as { [key: string]: Value };
    if (request.arguments === 'exit') process.exit(9);
    if (request.arguments === 'partial') { process.stdout.write(Buffer.from([0])); process.exit(0); }
    if (request.arguments === 'malformed') { process.stdout.write(frame({ status: 'made-up', value: null })); continue; }
    if (request.arguments === 'slow') await new Promise(resolve => setTimeout(resolve, 25));
    let response: Value = { status: 'success', value: request.arguments! };
    if (request.credential === 'wrong') response = { status: 'authentication', value: null };
    else if (op === 0 || op === 3) { handle = 'a'.repeat(64); response = { status: 'prepared', value: handle }; }
    else if (op === 1 && request.code !== handle) response = { status: 'failure', value: null };
    else if (op === 2) { handle = undefined; response = { status: 'invalidated', value: null }; }
    const reply = frame(response);
    // Exercise fragmentation independent of ordinary pipe write chunking.
    process.stdout.write(reply.subarray(0, 3)); process.stdout.write(reply.subarray(3));
  }
}
if (bytes.length) process.exitCode = 7;
