import type { Column, Projection, Statement } from './plan.ts';
import { SqlError } from './plan.ts';

export interface BendProgram { code: string; proof: string }
type Param = readonly [string, string];
const imports = `import Base
import ./Data.bend as D
import ./Semantics.bend as S
`;
const proofImports = `import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Logic.bend as L
import ./Requirements.bend as R
import ./Termination.bend as T
import ./Policy.bend as P
import ./Proofs.bend as H
import ./Configuration.bend as C
import ./Client.bend as Client
import ./Bindings.bend as B
`;
const list = (items: readonly string[]): string => items.reduceRight((tail, item) => `D.VList{${item}, ${tail}}`, 'D.VListEmpty{}');
const call = (name: string, params: readonly Param[]): string => `${name}(${params.map(([n]) => n).join(', ')})`;
const project = (columns: readonly Projection[], title = 'title', done = 'done'): string => {
  const values: Record<Column, string> = { id: 'D.VText{key}', title: `D.VText{${title}}`, completed: `D.VBool{${done}}`, owner: 'D.VText{owner}' };
  return list(columns.map(({ column }) => values[column]));
};

// Dependent proofs enumerate constructor alternatives explicitly. A wildcard
// leaves a residual type that the pinned checker cannot reduce through nested
// pattern matches, even when the corresponding action finishes immediately.
function otherReturns(exclude: 'text' | 'bool' | 'existence' | 'unit'): string {
  const cells: [string, string][] = [
    ['absent', 'D.VAbsent{}'], ['bool', 'D.VBool{value}'],
    ['int', 'D.VInt{high, low}'], ['text', 'D.VText{value}'],
    ['list-empty', 'D.VListEmpty{}'], ['list', 'D.VList{head, rest}'],
    ['record-empty', 'D.VRecordEmpty{}'], ['record', 'D.VRecord{name, value, rest}'],
  ];
  const patterns = cells.filter(([kind]) => kind !== exclude).map(([, cell]) => `S.Datum{D.Cell{${cell}}}`);
  patterns.push('S.Datum{D.RowAbsent{}}', 'S.Datum{D.Count{count}}', 'S.Datum{D.Keys{keys}}');
  if (exclude !== 'existence') patterns.push('S.Datum{D.Existence{exists}}');
  if (exclude !== 'unit') patterns.push('S.UnitValue{}');
  return patterns.map(pattern => `    case ${pattern}: Unit{}`).join('\n');
}

/** Emits ordinary Bend source and an independently checked universal certificate.
 * SQL values never enter source: they are decoded from execution arguments.
 * This first policy adapter targets the existing owner-isolated task schema.
 */
export function compileBend(statement: Statement): BendProgram {
  if (statement.table !== 'tasks') throw new SqlError('Only the tasks policy adapter is installed');
  const code: string[] = [imports, `def fields(+owner: String, +key: String, title: String, done: Bool) -> List<&2, D.Field>:
  [D.Field{"completed", D.VBool{done}}, D.Field{"id", D.VText{key}},
    D.Field{"owner", D.VText{owner}}, D.Field{"title", D.VText{title}}]

def result(rows: D.Value, count: U32) -> D.Value:
  D.VRecord{"rowCount", D.VInt{0, count}, D.VRecord{"rows", rows, D.VRecordEmpty{}}}

def append(rows: D.Value, row: D.Value) -> D.Value:
  match rows:
    case D.VList{head, rest}: D.VList{head, append(rest, row)}
    case _: D.VList{row, D.VListEmpty{}}
`];
  const proofs: string[] = [proofImports];
  function action(name: string, params: Param[], depth: number, body: string, proof: string): void {
    code.push(`def ${name}(${params.map(([n, t]) => `+${n}: ${t}`).join(', ')}) -> S.Action:\n${body}\n`);
    const tail = params.filter(([n]) => n !== 'owner');
    proofs.push(`def ${name}_safe(+owner: String, +kind: String${tail.map(([n, t]) => `, +${n}: ${t}`).join('')}) ->\n  H.Safe(${depth}n, D.Context{owner, kind}, Client.${call(name, params)}):\n${proof}\n`);
  }
  const finished = (row: string, count = 1): string => `S.Finish{result(${row}, ${count})}`;
  const zero = finished('D.VListEmpty{}', 0);
  const refuse = 'S.Refuse{D.VText{"unexpected SQL operation result"}}';
  let work: Param[];
  let analyze: string;
  let entry: string;
  let entryProof: string;
  let depth: number;

  if (statement.kind === 'insert') {
    if (statement.rows.length < 1 || statement.rows.length > 2) throw new SqlError('INSERT supports one or two rows');
    const n = statement.rows.length;
    depth = 2 * n + 1;
    work = Array.from({ length: n }, (_, i) => [[`key${i}`, 'String'], [`title${i}`, 'String'], [`done${i}`, 'Bool']] as Param[]).flat();
    const args = list(Array.from({ length: n }, (_, i) => list([`D.VText{key${i}}`, `D.VText{title${i}}`, `D.VBool{done${i}}`])));
    analyze = `    case ${args}: Work{${work.map(([name]) => name).join(', ')}}`;
    const params: Param[] = [['owner', 'String'], ...work, ['rows', 'D.Value']];
    const argsList = params.map(([name]) => name).join(', ');
    const proofArgs = ['owner', 'kind', ...work.map(([name]) => name), 'rows'].join(', ');
    for (let i = n - 1; i >= 0; i--) {
      const remaining = 2 * (n - i) + 1;
      const projected = project(statement.returning).replaceAll('D.VText{key}', `D.VText{key${i}}`).replaceAll('D.VText{title}', `D.VText{title${i}}`).replaceAll('D.VBool{done}', `D.VBool{done${i}}`);
      const nextRows = statement.returning.length ? `append(rows, ${projected})` : 'rows';
      const next = i === n - 1 ? finished(nextRows, n) : `insert_${i + 1}(${params.map(([name]) => name === 'rows' ? nextRows : name).join(', ')})`;
      const nextProof = i === n - 1 ? 'Unit{}' : `insert_${i + 1}_safe(${['owner', 'kind', ...work.map(([name]) => name), nextRows.replaceAll('append(', 'Client.append(')].join(', ')})`;
      action(`written_${i}`, [...params, ['r', 'S.Return']], remaining - 2,
        `  match r:\n    case S.UnitValue{}: ${next}\n    case _: ${refuse}`,
        `  match r:\n    case S.UnitValue{}: ${nextProof}\n${otherReturns('unit')}`);
      action(`exists_${i}`, [...params, ['r', 'S.Return']], remaining - 1,
        `  match r:\n    case S.Datum{D.Existence{False{}}}:\n      S.Access{D.DefineRow{D.Application{owner}, key${i}, fields(owner, key${i}, title${i}, done${i})},\n        r => written_${i}(${argsList}, r)}\n    case S.Datum{D.Existence{True{}}}: S.Refuse{D.VText{"duplicate key"}}\n    case _: ${refuse}`,
        `  match r:\n    case S.Datum{D.Existence{False{}}}:\n      L.Both{P.Both{{==}, {==}}, r => written_${i}_safe(${proofArgs}, r)}\n    case S.Datum{D.Existence{True{}}}: Unit{}\n${otherReturns('existence')}`);
      action(`insert_${i}`, params, remaining,
        `  S.Access{D.ViewExistence{D.Application{owner}, key${i}}, r => exists_${i}(${argsList}, r)}`,
        `  L.Both{{==}, r => exists_${i}_safe(${proofArgs}, r)}`);
    }
    entry = `insert_0(owner, ${work.map(([name]) => name).join(', ')}, D.VListEmpty{})`;
    entryProof = `insert_0_safe(id, kind, ${work.map(([name]) => name).join(', ')}, D.VListEmpty{})`;
  } else {
    depth = statement.kind === 'select' ? 3 : 4;
    work = [['key', 'String']];
    if (statement.kind === 'update') work.push(['replacement_title', 'Maybe<&2, String>'], ['replacement_done', 'Maybe<&2, Bool>']);
    analyze = statement.kind === 'update'
      ? [
          ['D.VAbsent{}', 'D.VAbsent{}', 'None{}', 'None{}'],
          ['D.VText{title}', 'D.VAbsent{}', 'Some{title}', 'None{}'],
          ['D.VAbsent{}', 'D.VBool{done}', 'None{}', 'Some{done}'],
          ['D.VText{title}', 'D.VBool{done}', 'Some{title}', 'Some{done}'],
        ].map(([title, done, t, d]) => `    case ${list([list(['D.VText{key}', title!, done!])])}: Work{key, ${t}, ${d}}`).join('\n')
      : `    case ${list([list(['D.VText{key}'])])}: Work{key}`;
    const params: Param[] = [['owner', 'String'], ...work];
    const titleParams: Param[] = [...params, ['title', 'String']];
    const fullParams: Param[] = [...titleParams, ['done', 'Bool']];
    const columns = statement.kind === 'select' ? statement.columns : statement.returning;
    const rows = columns.length ? list([project(columns)]) : 'D.VListEmpty{}';
    if (statement.kind === 'update') {
      code.push(`def use_title(replacement: Maybe<&2, String>, old: String) -> String:\n  match replacement:\n    case Some{value}: value\n    case None{}: old\n\ndef use_done(replacement: Maybe<&2, Bool>, old: Bool) -> Bool:\n  match replacement:\n    case Some{value}: value\n    case None{}: old\n`);
    }
    let chosen: string;
    let chosenProof: string;
    if (statement.kind === 'select') {
      chosen = finished(rows); chosenProof = 'Unit{}';
    } else {
      action('written', [...fullParams, ['r', 'S.Return']], 1,
        `  match r:\n    case S.UnitValue{}: ${finished(rows)}\n    case _: ${refuse}`,
        `  match r:\n    case S.UnitValue{}: Unit{}\n${otherReturns('unit')}`);
      const newParams = statement.kind === 'update' ? fullParams.map(([name]) => name === 'title' ? 'use_title(replacement_title, title)' : name === 'done' ? 'use_done(replacement_done, done)' : name).join(', ') : fullParams.map(([name]) => name).join(', ');
      const operation = statement.kind === 'update'
        ? 'D.DefineRow{D.Application{owner}, key, fields(owner, key, use_title(replacement_title, title), use_done(replacement_done, done))}'
        : 'D.RemoveRow{D.Application{owner}, key}';
      chosen = `S.Access{${operation}, r => written(${newParams}, r)}`;
      const writePermission = statement.kind === 'update' ? 'P.Both{{==}, {==}}' : '{==}';
      const proofNewParams = ['owner', 'kind', ...fullParams.filter(([name]) => name !== 'owner').map(([name]) => name === 'title' && statement.kind === 'update' ? 'Client.use_title(replacement_title, title)' : name === 'done' && statement.kind === 'update' ? 'Client.use_done(replacement_done, done)' : name)].join(', ');
      chosenProof = `L.Both{${writePermission}, r => written_safe(${proofNewParams}, r)}`;
    }
    action('got_done', [...titleParams, ['r', 'S.Return']], depth - 2,
      `  match r:\n    case S.Datum{D.Cell{D.VBool{done}}}: ${chosen}\n    case _: ${refuse}`,
      `  match r:\n    case S.Datum{D.Cell{D.VBool{done}}}: ${chosenProof}\n${otherReturns('bool')}`);
    action('got_title', [...params, ['r', 'S.Return']], depth - 1,
      `  match r:\n    case S.Datum{D.Cell{D.VText{title}}}:\n      S.Access{D.ReadCell{D.Application{owner}, key, "completed"}, r => got_done(${titleParams.map(([name]) => name).join(', ')}, r)}\n    case S.Datum{D.RowAbsent{}}: ${zero}\n    case _: ${refuse}`,
      `  match r:\n    case S.Datum{D.Cell{D.VText{title}}}:\n      L.Both{{==}, r => got_done_safe(owner, kind, ${titleParams.filter(([name]) => name !== 'owner').map(([name]) => name).join(', ')}, r)}\n    ${otherReturns('text')}`);
    action('query', params, depth,
      `  S.Access{D.ReadCell{D.Application{owner}, key, "title"}, r => got_title(${params.map(([name]) => name).join(', ')}, r)}`,
      `  L.Both{{==}, r => got_title_safe(owner, kind, ${params.filter(([name]) => name !== 'owner').map(([name]) => name).join(', ')}, r)}`);
    entry = `query(owner, ${work.map(([name]) => name).join(', ')})`;
    entryProof = `query_safe(id, kind, ${work.map(([name]) => name).join(', ')})`;
  }
  const commandFields = work.map(([name, type]) => `${name}: ${type}`).join(', ');
  code.splice(1, 0, `type Command is Data:\n  Work{${commandFields}}\n  Invalid{}\n`);
  code.push(`def analyze(args: D.Value) -> Command:\n  match args:\n${analyze}\n    case _: Invalid{}\n\ndef command(+owner: String, p: Command) -> S.Action:\n  match p:\n    case Work{${work.map(([name]) => `+${name}`).join(', ')}}: ${entry}\n    case Invalid{}: S.Refuse{D.VText{"invalid SQL arguments"}}\n\ndef start(ctx: D.Context, args: D.Value) -> S.Action:\n  command(D.context_id(ctx), analyze(args))\n\ndef program() -> S.Program:\n  S.Program{start}\n`);
  proofs.push(`def command_safe(ctx: D.Context, p: Client.Command) -> H.Safe(${depth}n, ctx, Client.command(D.context_id(ctx), p)):
  match ctx p:
    case D.Context{+id, +kind} Client.Work{${work.map(([name]) => `+${name}`).join(', ')}}: ${entryProof}
    case D.Context{id, kind} Client.Invalid{}: Unit{}

def program_safe(+ctx: D.Context, args: D.Value) -> H.Safe(${depth}n, ctx, S.start(Client.program(), ctx, args)):
  command_safe(ctx, Client.analyze(args))

def owners_initial(-s: D.State, valid: R.Valid(C.config(), s)) -> P.Owners(s):
  match valid:
    case L.Both{structure, L.Both{owners, remaining}}: owners

def certify(+ctx: D.Context, +args: D.Value, -code: String, +s: D.State,
  valid: R.Valid(C.config(), s), identity: {D.context_present(s, ctx) == True{} : Bool}, +n: Nat) ->
  R.SafetyTrace(S.execute(n, Client.program(), C.schema(), s, ctx, args), C.config(), s, ctx, code, args):
  H.execution_trace(S.execute(n, Client.program(), C.schema(), s, ctx, args),
    C.schema(), C.limits(), C.environment(), s, ctx, code, args,
    H.rewind(ctx, S.execute(n, Client.program(), C.schema(), s, ctx, args),
      T.observe(n, S.start(Client.program(), ctx, args), C.schema(), s, Nil{}),
      Equal.sym(S.Trace, T.observe(n, S.start(Client.program(), ctx, args), C.schema(), s, Nil{}),
        S.execute(n, Client.program(), C.schema(), s, ctx, args),
        T.reference(n, S.start(Client.program(), ctx, args), C.schema(), s)),
      H.safe(${depth}n, n, S.start(Client.program(), ctx, args), ctx, C.schema(), s, Nil{},
        program_safe(ctx, args), P.Both{owners_initial(s, valid), P.Both{identity, Unit{}}})))

def B.certificate(ctx, args, s, valid, identity, n):
  certify(ctx, args, B.code(), s, valid, identity, n)

def B.terminates(s, ctx, args):
  +ctx = ctx
  +args = args
  T.program_finite(${depth}n, Client.program(), C.schema(), s, ctx, args,
    H.finite(${depth}n, S.start(Client.program(), ctx, args), ctx, program_safe(ctx, args)))
`);
  return { code: code.join('\n'), proof: proofs.join('\n') };
}
