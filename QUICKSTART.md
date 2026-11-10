# Your first durable TypeScript application

This walkthrough uses the existing task application: its schema, identity-based
laws, program, initial-state proof and request certificate are all Bend. A small
Node/TypeScript client starts the ordinary JayDB2 executable and exchanges its
existing binary protocol. No database feature or proof rule is added.

## 1. Install once

Follow [INSTALL.md](INSTALL.md) for the Linux x86-64 prerequisites and pinned Bend
distribution, then run:

```sh
make build
node --version
```

Use Node 24. The task app runs `.ts` directly using Node's type stripping; there
is no npm dependency or Python process in its runtime path. The first request
checks and compiles the program and may take several seconds.

## 2. Save a real task

Choose a workspace that does not already exist:

```sh
node applications/tasks/tasks.ts \
  --workspace .build/tasks/first --storage-mode create \
  --command save t1 "Try JayDB2 from TypeScript"
```

Expected response:

```json
{"status":"success","value":"t1"}
```

The process has now exited. Its complete database image is in
`.build/tasks/first/db/`, and its frozen example modules are in `app/` beside
that directory. Alice's task is saved on disk.

## 3. Reopen, update and read

```sh
node applications/tasks/tasks.ts \
  --workspace .build/tasks/first --storage-mode open --command view t1
node applications/tasks/tasks.ts \
  --workspace .build/tasks/first --storage-mode open --command conclude t1
node applications/tasks/tasks.ts \
  --workspace .build/tasks/first --storage-mode open --command view t1
```

The final response is:

```json
{"status":"success","value":{"completed":true,"id":"t1","owner":"alice","title":"Try JayDB2 from TypeScript"}}
```

Every command starts a fresh instance, reopens the same image, authenticates the
request and checks the actual program/certificate. Open neither reads nor
recreates the seed. It requires the same executable and public environment;
after development changes, choose a new disposable workspace. There is no
migration or compatibility layer.

## 4. Try isolation and rollback

```sh
node applications/tasks/tasks.ts \
  --workspace .build/tasks/first --storage-mode open \
  --credential bob-token --command list
# {"status":"success","value":[]}

node applications/tasks/tasks.ts \
  --workspace .build/tasks/first --storage-mode open \
  --command cancel t1 "Discard this update" false
# {"status":"refusal","value":"cancelled"}; exit status 2

node applications/tasks/tasks.ts \
  --workspace .build/tasks/first --storage-mode open --command view t1
```

The refused write leaves Alice's completed task unchanged. Alice and Bob may
use the same task ID in their separate tables. These are **public example
credentials**, suitable for this local demonstration. Provisioning real users
and application policies is an administrator responsibility.

The CLI exits 0 on success, 2 on a canonical non-success response, and 1 on a
startup/client/transport error. Loss of a response can leave a write's outcome
unknown. The client never silently retries it. To keep one instance open for
several commands, use the existing Python terminal client:

```sh
python3 -B applications/tasks/app.py \
  --workspace .build/tasks/first --storage-mode open
```

Exit one client before opening that workspace from another: one service owns a
storage directory at a time.

## 5. Start your own program

Export a checked example without editing the database:

```sh
python3 -B examples/starter/create.py .build/my-app --profile crud
(ulimit -s unlimited
 flock /tmp/jaydb2-experiments-heavy.lock python3 -B examples/starter/check.py .build/my-app)
```

This gives you editable application sources and certificates. It runs both
official checkers and real requests, including rejected law-breaking mutations.
The [program/proof guide](docs/programs-and-proofs.md) explains which application
files to edit and how the existing composition lemmas apply. A second
`conditional` profile covers conditional and batch operations.

For your own TypeScript host application, see the
[client API and example](clients/typescript/README.md). The package can be built
and installed locally into a separate TS project; publishing to npm is not
required. It handles ordinary requests and optional prepared handles, while
your Bend program and proof remain explicit inputs. Requests execute one at a
time; `--threads N` controls the CPU workers within each native process.

## Troubleshooting

- `EEXIST` on create: reopen the existing workspace, or choose a fresh path.
  Create never resets a directory. A failed create can leave a partial workspace.
- An incompatible saved image: use its original exact build/environment or a
  new development workspace. Open never silently falls back to empty data.
- Authentication/refusal/certificate response: inspect its status and the
  server's stderr. These differ from transport failure or an unknown outcome.
- Unsupported stack limit/toolchain: follow the prerequisite checks in
  [INSTALL.md](INSTALL.md); the application does not substitute a checker/runtime.

See [the task application](applications/tasks/README.md) for all commands and
[verification](docs/verification.md) for smoke and release checks.
