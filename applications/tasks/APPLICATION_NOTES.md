# Task application usability notes

The reference task application exercises existing JayDB2 features. Its Bend
program, administrator laws, initial state and proofs are unchanged by these
accessories. The TypeScript CLI uses the optional TypeScript client and submits
ordinary certified requests; the Python terminal client remains available.

## Friction addressed

| Observed developer workflow | Accessory change |
| --- | --- |
| The original terminal client always created a temporary RAM instance and lost tasks on exit. | Explicit persistent workspace `create` and `open`, with no default reset. |
| Setting up an application meant packaging its imported proof/library modules by hand. | Both clients package the exact existing application once into `workspace/app`. Open reuses those bytes. |
| A TypeScript application had no ready task-client example. | `tasks.ts` imports the thin TypeScript client directly on Node 24, with no Python subprocess or npm build at runtime. |
| Reopening could accidentally be confused with reinitializing from the seed. | Open sends no `--seed`, copies no modules, and works after the staged seed is removed. |
| An interactive-only interface was awkward for scripts or comparing restart results. | `--command` emits one JSON response with documented success/non-success/transport exit codes. |
| The default runtime worker count was excessive for tiny sequential task commands on a large machine. | These application CLIs default to one native worker, with an explicit override. The database default is unchanged. |

## Reproducible workflow

Build and install the pinned tools using [INSTALL.md](../../INSTALL.md). Use a
new ignored workspace for this session:

```sh
node applications/tasks/tasks.ts --workspace .build/tasks/review --storage-mode create --command save polish "Review quickstart"
node applications/tasks/tasks.ts --workspace .build/tasks/review --storage-mode open --command conclude polish
node applications/tasks/tasks.ts --workspace .build/tasks/review --storage-mode open --command view polish
python3 -B applications/tasks/app.py --workspace .build/tasks/review --storage-mode open
```

The final command opens the same persisted tasks interactively. `view polish`
should show the original title and `completed: true`. Bob's default table is
separate; switching with `user bob-token` and listing does not reveal Alice's
record. A `cancel` operation refuses after provisional work, so the prior saved
record remains.

These example credentials are public, and the app still has two fixed users.
This is a useful local development task list rather than a production account
system. Saved images require their exact controller/environment. On application
or database upgrades, create a new disposable development workspace; there is no
implicit migration, backward compatibility adapter or automatic data reset.

## Acceptance record

The seven lightweight workspace/parser/API checks passed locally using
`python3 -B -m unittest tests.accessories.test_tasks -v`. They require no Bend
distribution or native build. `node --check applications/tasks/tasks.ts` and
`clients/typescript/node_modules/.bin/tsc -p applications/tasks/tsconfig.json`
also passed. The latter uses the thin client package's development-only compiler
and Node types; the TypeScript application has no runtime npm dependencies.

The separate native acceptance case is
`python3 -B -m unittest tests.accessories.test_tasks_native -v`, run under the
shared heavy-work lock after building JayDB2. It checks the actual TypeScript
and Python clients, durable restart without a seed, exact task contents,
completion, refusal rollback, Bob isolation, invalid credentials, second-create
rejection and unchanged staged configuration. Its final run is coordinated with
the accessory release gate; do not infer a completed native result from this
static test description.

A scripted acceptance session establishes correctness of the demonstrated
workflow. It is not evidence of long-term adoption, external users or sustained
daily use. Future usability issues should be recorded from actual sessions.
