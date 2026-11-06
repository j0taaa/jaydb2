# Optional TypeScript client

A small Node 24+ client for the existing JayDB2 stdin/stdout protocol. It changes
no database behavior. Runtime dependencies: none. Linux x86-64 and the pinned
database toolchain are still required to run the database itself.

## Use from a separate TypeScript application

Build and pack the client in this checkout:

```sh
cd clients/typescript
npm ci
npm run build
npm pack
```

Then, in your own application directory:

```sh
npm install /absolute/path/to/jaydb2/clients/typescript/jaydb2-client-0.1.0.tgz
npm install --save-dev typescript@5.9.3 @types/node@24.19.0
```

Use `"type": "module"` in your application's `package.json`. A minimal
`tsconfig.json` uses `"target": "ES2022"`, `"module": "NodeNext"`,
`"moduleResolution": "NodeNext"`, `"strict": true`, and an `outDir`.
The tarball exports built ESM JavaScript plus declarations, so consumers do not
need this repository's source paths or TypeScript runtime stripping. Publishing
to a registry is not needed, and no registry publication is part of this change.

```ts
import { Client } from '@jaydb2/client';
import { readFile } from 'node:fs/promises';

const root = '/absolute/path/to/jaydb2'; // Install tools and make build first.
const client = Client.spawn({
  command: `${root}/jaydb2`,
  args: ['--configuration', `${root}/examples/access/Configuration.bend`,
         '--seed', `${root}/examples/access/Seed.bend`, '--threads', '1'],
  cwd: root,
});
try {
  const response = await client.request({
    credential: 'alice-token', // Public example credential; choose your own.
    code: await readFile(`${root}/examples/access/Client.bend`, 'utf8'),
    proof: await readFile(`${root}/examples/access/ClientProof.bend`, 'utf8'),
    arguments: 'alice-new',
  });
  console.log(response); // {status:'success', value:'alice-new'}
} finally {
  await client.close();
}
```

This access-example operation changes Alice's credential. Every later call must
send the current credential. It is not a general-purpose application operation.
The [persistent task application](../../applications/tasks/README.md) shows a
real TS application with ordinary certified CRUD and separate create/open runs.

Inside this checkout on Node 24, applications can instead import
`./clients/typescript/src/index.ts` by a suitable relative path. This uses Node's
ordinary TypeScript type stripping and has no runtime install step.

## Requests, preparation and responses

- `Client.spawn({command, args?, cwd?, env?, stderr?})` starts one session with
  piped stdin/stdout and inherited stderr by default. Arguments are an array;
  no shell is used. The owned process has its own process group on Linux.
- `new Client({input, output, completion?})` attaches to existing binary Node
  streams. `input` is the writable request pipe; `output` is the readable
  response pipe. Do not call `setEncoding` on the response stream. A supplied
  process-completion promise must reject on unsuccessful exit.
- `request({credential, code, proof, arguments})` sends an ordinary request.
- `prepare({credential, code, proof, readOnly?})` sends opcode 0, or opcode 3
  for a separately read-certified program. It returns the actual control
  response; check `status === 'prepared'` and `typeof value === 'string'` before
  using the handle. A universal certificate is required; the client does not
  convert, fabricate or prove it. Read preparation needs the additional actual
  whole-program read-only certificate.
- `execute({credential, handle, arguments})` and
  `invalidate({credential, handle})` use the existing handle protocol.
- `await close()` ends stdin, drains all accepted responses and waits for owned
  process exit. It has no deadline. A canonical `refusal`, `authentication`,
  `certificate`, `data`, `limit` or `failure` is a returned response, not a
  JavaScript exception. Preparation/invalidation return their metadata receipts.

Concurrent calls are pipelined in invocation order and responses are matched
FIFO. This does not promise concurrent database execution. Prepared handles
belong to one instance and are lost on restart. The client does not reconnect,
retry, reprepare or cache credentials. Another user can use a valid handle with
their own credential, subject to the normal current authentication and laws.

## Values and failure semantics

`Value` supports null, booleans, strings, arrays, plain records and signed int64.
**All decoded integers are bigint**, including small ones. Encoding accepts
bigint across the full int64 range, plus safe integral JS numbers as a convenience.
Use `123n` for exact integers; fractional, infinite and unsafe numbers reject.
`JSON.stringify` needs an explicit bigint conversion if you display such values.

Strings preserve BOM and exact Unicode scalar sequences. Isolated UTF-16
surrogates reject rather than being replaced. Records use the database's ASCII
field-name grammar and canonical order; prototype-sensitive names remain data.
Getters, exotic objects, sparse arrays and cycles reject. Exported `encode`,
`decode`, `frame`, `unframe` and `preparedFrame` expose the existing wire format.

Transport failures and malformed peer responses reject pending calls with
`TransportError` or `ProtocolError` (both extend `JaydbError` and carry
`outcome: 'unknown'`). **A lost response is not a rollback receipt.** A write
may already be durable; retry only according to your application's explicit
receipt protocol. `abort()` tears down the pipes and owned process group, with
the same unknown-outcome semantics. It cannot undo a commit.

Local input validation and a full pending queue reject a new call before writing
it. The default bounds are 64 outstanding calls and 16 MiB per response body;
configure `maxPendingRequests` and `maxResponseBytes` on either constructor.
These are client allocation policies, separate from administrator database size
limits. The parser handles fragmented/coalesced frames and checks declared
lengths before allocation. The stream constructor does not own external process
cleanup; the caller must implement that if needed.

## Checks

```sh
npm ci
npm run check
npm test
npm run build
```

Cheap tests need Node, npm and Python, but no Bend/Clang or `.tools`. They include
an independent Python wire comparison, all int64 edges, malformed Unicode and
records, deep values, fragmented/coalesced responses, EOF/write/process failures,
pending bounds, fake-peer session lifecycle, and a packed package installed and
type-checked in a separate temporary TS application. Development tools are pinned
in `package-lock.json`; `npm test` does not change the database.

After installing/building the actual database, the separate native gate is:

```sh
flock /tmp/jaydb2-experiments-heavy.lock npm run test:integration
```

The caller holds that lock once; the integration script does not acquire it.
It checks ordinary and prepared calls, fresh per-call credentials, refusal,
invalidation and instance-local handles against the real executable and proofs.
Fake-peer tests establish client transport behavior; they are not claimed as
evidence about the database's authorization or publication behavior.
