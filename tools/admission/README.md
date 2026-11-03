# Admission

The gate receives a program and its certificate for the configuration, identity, and arguments fixed by the host. Registered dependencies, source bytes, and certificate targets must match exactly. Metas, open laws, unsafe code, and client external effects are rejected, including in unused definitions.

```js
import { admitSubmission, emitC } from './index.mjs';
const admitted = await admitSubmission(hostManifest);
const c = emitC(admitted);
```

The public handle exposes `sources` and `report`. The checked Book stays private and is the same object passed to the official compiler. There is no API for changing declarations after checking. `configurationLimits(admitted)` reads the three logical sizes for the service.

## Official tools

1. Preflight fixes source bytes and authorized dependencies before running the frontend.
2. The official Bend 2.0.39 checker checks the source.
3. Official Safe translates the declarations; original BendTT checks that payload.
4. The official compiler emits C from the same Book without rereading submission sources.

Sources and the kernel are checked against `toolchain.lock.json`. Official TypeScript modules are loaded by stripping TypeScript syntax with Node, without a semantic patch. JayDB does not change Bend conversion, templates, quantities, logical rules, fuel, or runtime.

There are no alternative Safe layouts, custom instance closure, generated `source_links`, structural evaluators, or attempts through a second path after rejection. A form not represented by official Safe is not a proof of falsity; the database does not change the translator to admit it.

Application bindings still require the actual configuration, code, context, and arguments. Published state is not copied into the compilation directory.

The optional host manifest mode `certificateMode: 'universal'` requires an
exact certificate quantified over `ctx` and `args`, and rejects all transitive
client captures of concrete `Instance.context`/`Instance.arguments`. This is
used by [prepared programs](../service/PREPARED_PROGRAMS.md); the default
`concrete` mode retains per-call certificates. Both modes use the same official
checkers, source binding, purity policy and checked-Book compilation.

## Kernel boundary

`admitKernel` admits trusted JayDB wrappers. Only their registered foreign declarations receive integration permission; clients do not receive that capability. Initialization requires a seed-validity proof for the actual configuration. The host compiles official C without rewriting it and runs each call in a child process, retaining publication in the host.

Use the commands in the root README. There is no derived verifier installation, stack addon, physical budget, or per-request deadline. The official tools' own limitations remain unchanged. The gate does not claim general semantic preservation or the complete executable's `Contract`.

The launcher uses the public `node --stack_size=65536` option for official Safe. The profile requires an unlimited Linux hard stack limit and raises the soft limit to unlimited before executing Node. This is a helper execution setting; Bend and V8 sources are unchanged.
