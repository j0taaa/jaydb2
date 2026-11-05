# Read certificates describe all continuations; actual authorization remains
# the ordinary administrator certificate. Host effects and ordering are a bridge.
import Base
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/Logic.bend as L
import ../src/ReadOnly.bend as RO
import ../src/Termination.bend as T

def finite_prefix(n: Nat, a: S.Action, h: RO.Action(n, a), m: Nat) -> RO.Prefix(m, a):
  match n:
    case 0n: Empty.absurd(RO.Prefix(m, a), h)
    case 1n+k:
      match a:
        case S.Finish{v}:
          match m:
            case 0n: Unit{}
            case 1n+j: Unit{}
        case S.Refuse{v}:
          match m:
            case 0n: Unit{}
            case 1n+j: Unit{}
        case S.Access{o, resume}:
          match h:
            case L.Both{op, next}:
              match m:
                case 0n: Unit{}
                case 1n+j: L.Both{op, +r => finite_prefix(k, resume(r), next(r), j)}

def NoChange(r: D.ResultOp) -> Type:
  match r:
    case D.Changed{w}: Empty
    case _: Unit

def cell_result(v: Maybe<&2, D.Value>) -> NoChange(D.result_cell(v)):
  match v:
    case None{}: Unit{}
    case Some{x}: Unit{}

def row_result(row: Maybe<&2, D.Row>, column: String) -> NoChange(D.read_row(row, column)):
  match row:
    case None{}: Unit{}
    case Some{D.Row{k, fs}}: cell_result(D.find_field(fs, column))

def column_result(col: Maybe<&2, D.Column>, row: Maybe<&2, D.Row>, name: String) ->
  NoChange(D.read_column(col, row, name)):
  match col:
    case None{}: Unit{}
    case Some{x}: row_result(row, name)

def resolved_result(o: D.Operation, r: Maybe<&2, D.Resolved>, s: D.State,
  h: RO.Operation(o)) -> NoChange(D.operate_resolved(o, r, s)):
  match o:
    case D.ReadCell{c, k, +name}:
      match r:
        case None{}: Unit{}
        case Some{D.Resolved{D.SchemaTable{en, pk, cs}, ls}}:
          column_result(D.find_column(cs, name), D.find_row(ls, k), name)
    case D.ViewExistence{c, k}:
      match r:
        case None{}: Unit{}
        case Some{D.Resolved{e, ls}}: Unit{}
    case D.CountRows{c}:
      match r:
        case None{}: Unit{}
        case Some{D.Resolved{e, ls}}: Unit{}
    case D.EnumerateKeys{c}:
      match r:
        case None{}: Unit{}
        case Some{D.Resolved{e, ls}}: Unit{}
    case D.DefineRow{c, k, fs}: Empty.absurd(NoChange(D.operate_resolved(D.DefineRow{c, k, fs}, r, s)), h)
    case D.DefineColumn{c, k, name, v}: Empty.absurd(NoChange(D.operate_resolved(D.DefineColumn{c, k, name, v}, r, s)), h)
    case D.RemoveRow{c, k}: Empty.absurd(NoChange(D.operate_resolved(D.RemoveRow{c, k}, r, s)), h)

def address_result(ok: Bool, e: D.Schema, +s: D.State, +o: D.Operation,
  h: RO.Operation(o)) -> NoChange(D.operate_address(ok, e, s, o)):
  match ok:
    case False{}: Unit{}
    case True{}:
      +c = D.collection_op(o)
      resolved_result(o, D.resolve_parts(D.schema_collection(c, e), D.rows_collection(c, s)), s, h)

law read_operation_cannot_change:
  for +o: D.Operation
  for e: D.Schema
  for s: D.State
  for h: RO.Operation(o)
  NoChange(D.operate(e, s, o))
def read_operation_cannot_change(o, e, s, h):
  address_result(D.address_op_valid(o), e, s, o, h)

def result_state(r: D.ResultOp, +n: Nat, +s: D.State, +e: D.Schema,
  +o: D.Operation, -k: S.Return -> S.Action, +ts: List<&2, S.OperationEvent>,
  no_change: NoChange(r),
  rec: @v: S.Return -> @events: List<&2, S.OperationEvent> ->
    {S.state_execution_trace(T.observe(n, k(v), e, s, events)) == s : D.State}) ->
  {S.state_execution_trace(S.resume_execution_trace(n, S.apply(r, s, o, k), e, ts)) == s : D.State}:
  match r:
    case D.FailureData{}:
      %Equal.sym(S.Trace, S.resume_execution_trace(n, S.OperationFailed{s, S.OperationEvent{o, S.ErrorOfData{}}}, e, ts), S.Final{s, S.append(ts, S.OperationEvent{o, S.ErrorOfData{}}), S.response_error(S.DataError{})}, T.failure_of_operation(n, s, S.OperationEvent{o, S.ErrorOfData{}}, e, ts)) :
        {S.state_execution_trace(_) == s : D.State}
      {==}
    case D.Observed{+obs}:
      %Equal.sym(S.Trace, S.resume_execution_trace(n, S.Continue{s, k(S.Datum{obs}), S.OperationEvent{o, S.Reading{obs}}}, e, ts), T.observe(n, k(S.Datum{obs}), e, s, S.append(ts, S.OperationEvent{o, S.Reading{obs}})), T.continuation(n, s, k(S.Datum{obs}), S.OperationEvent{o, S.Reading{obs}}, e, ts)) :
        {S.state_execution_trace(_) == s : D.State}
      rec(S.Datum{obs}, S.append(ts, S.OperationEvent{o, S.Reading{obs}}))
    case D.Changed{w}: Empty.absurd(
      {S.state_execution_trace(S.resume_execution_trace(n, S.apply(D.Changed{w}, s, o, k), e, ts)) == s : D.State}, no_change)

law prefix_preserves_state:
  for n: Nat
  for a: S.Action
  for +e: D.Schema
  for +s: D.State
  for +ts: List<&2, S.OperationEvent>
  for h: RO.Prefix(n, a)
  {S.state_execution_trace(T.observe(n, a, e, s, ts)) == s : D.State}
def prefix_preserves_state(n, a, e, s, ts, h):
  match n:
    case 0n: {==}
    case 1n+k:
      match a:
        case S.Finish{v}:
          %Equal.sym(S.Trace, S.resume_execution_trace(k, S.Stopped{s, S.Response{S.Success{}, v}}, e, ts), S.Final{s, ts, S.Response{S.Success{}, v}}, T.stopped(k, s, S.Response{S.Success{}, v}, e, ts)) : {S.state_execution_trace(_) == s : D.State}
          {==}
        case S.Refuse{v}:
          %Equal.sym(S.Trace, S.resume_execution_trace(k, S.Stopped{s, S.Response{S.Refusal{}, v}}, e, ts), S.Final{s, ts, S.Response{S.Refusal{}, v}}, T.stopped(k, s, S.Response{S.Refusal{}, v}, e, ts)) : {S.state_execution_trace(_) == s : D.State}
          {==}
        case S.Access{+o, resume}:
          L.Both{op, next} = h
          +remaining = k
          result_state(D.operate(e, s, o), remaining, s, e, o, resume, ts,
            read_operation_cannot_change(o, e, s, op),
            +r => events => prefix_preserves_state(remaining, resume(r), e, s, events, next(r)))

law finite_preserves_state:
  for depth: Nat
  for a: S.Action
  for +n: Nat
  for +e: D.Schema
  for +s: D.State
  for +ts: List<&2, S.OperationEvent>
  for h: RO.Action(depth, a)
  {S.state_execution_trace(T.observe(n, a, e, s, ts)) == s : D.State}
def finite_preserves_state(depth, a, n, e, s, ts, h):
  match depth:
    case 0n: Empty.absurd({S.state_execution_trace(T.observe(n, a, e, s, ts)) == s : D.State}, h)
    case 1n+d:
      match a:
        case S.Finish{v}:
          match n:
            case 0n: {==}
            case 1n+k:
              %Equal.sym(S.Trace, S.resume_execution_trace(k, S.Stopped{s, S.Response{S.Success{}, v}}, e, ts), S.Final{s, ts, S.Response{S.Success{}, v}}, T.stopped(k, s, S.Response{S.Success{}, v}, e, ts)) : {S.state_execution_trace(_) == s : D.State}
              {==}
        case S.Refuse{v}:
          match n:
            case 0n: {==}
            case 1n+k:
              %Equal.sym(S.Trace, S.resume_execution_trace(k, S.Stopped{s, S.Response{S.Refusal{}, v}}, e, ts), S.Final{s, ts, S.Response{S.Refusal{}, v}}, T.stopped(k, s, S.Response{S.Refusal{}, v}, e, ts)) : {S.state_execution_trace(_) == s : D.State}
              {==}
        case S.Access{+o, resume}:
          match n:
            case 0n: {==}
            case 1n+k:
              L.Both{op, next} = h
              +remaining = k
              result_state(D.operate(e, s, o), remaining, s, e, o, resume, ts,
                read_operation_cannot_change(o, e, s, op),
                +r => events => finite_preserves_state(d, resume(r), remaining, e, s, events, next(r)))

def witnessed_state(+n: Nat, p: S.Program, +e: D.Schema, +s: D.State,
  +ctx: D.Context, +args: D.Value,
  witness: &depth: Nat -> RO.Action(depth, S.start(p, ctx, args))) ->
  {S.state_execution_trace(S.execute(n, p, e, s, ctx, args)) == s : D.State}:
  match witness:
    case (depth, evidence):
      %T.reference(n, S.start(p, ctx, args), e, s) : {S.state_execution_trace(_) == s : D.State}
      finite_preserves_state(depth, S.start(p, ctx, args), n, e, s, Nil{}, evidence)

law program_preserves_every_prefix:
  for +n: Nat
  for p: S.Program
  for +e: D.Schema
  for +s: D.State
  for +ctx: D.Context
  for +args: D.Value
  for certificate: RO.Program(p)
  {S.state_execution_trace(S.execute(n, p, e, s, ctx, args)) == s : D.State}
def program_preserves_every_prefix(n, p, e, s, ctx, args, certificate):
  witnessed_state(n, p, e, s, ctx, args, certificate(ctx, args))

type Call is Type:
  Call{program: S.Program, context: D.Context, arguments: D.Value, prefix: Nat}

def Certificates(calls: List<Call>) -> Type:
  match calls:
    case Nil{}: Unit
    case Con{Call{p, ctx, args, n}, rest}: L.E<RO.Program(p), Certificates(rest)>

# Programs are linear values in the pure model, so a heterogeneous batch
# retains one program per call. Evidence is required for every entry.
def frozen(calls: List<Call>, +e: D.Schema, +s: D.State) -> List<&2, S.Trace>:
  match calls:
    case Nil{}: Nil{}
    case Con{Call{p, ctx, args, n}, rest}:
      S.execute(n, p, e, s, ctx, args) <> frozen(rest, e, s)

def serial(calls: List<Call>, +e: D.Schema, s: D.State) -> List<&2, S.Trace>:
  match calls:
    case Nil{}: Nil{}
    case Con{Call{p, ctx, args, n}, rest}:
      +trace = S.execute(n, p, e, s, ctx, args)
      trace <> serial(rest, e, S.state_execution_trace(trace))

law frozen_batch_refines_serial:
  for +e: D.Schema
  for +s: D.State
  for calls: List<Call>
  for certificates: Certificates(calls)
  {serial(calls, e, s) == frozen(calls, e, s) : List<&2, S.Trace>}
def frozen_batch_refines_serial(e, s, calls, certificates):
  match calls:
    case Nil{}: {==}
    case Con{Call{p, +ctx, +args, +n}, rest}:
      L.Both{certificate, remaining} = certificates
      %Equal.sym(D.State, S.state_execution_trace(S.execute(n, p, e, s, ctx, args)), s,
        program_preserves_every_prefix(n, p, e, s, ctx, args, certificate)) :
        {S.execute(n, p, e, s, ctx, args) <> serial(rest, e, _) ==
          S.execute(n, p, e, s, ctx, args) <> frozen(rest, e, s) : List<&2, S.Trace>}
      %Equal.sym(List<&2, S.Trace>, serial(rest, e, s), frozen(rest, e, s),
        frozen_batch_refines_serial(e, s, rest, remaining)) :
        {S.execute(n, p, e, s, ctx, args) <> _ ==
          S.execute(n, p, e, s, ctx, args) <> frozen(rest, e, s) : List<&2, S.Trace>}
      {==}

law reads_preserve_fresh_authentication:
  for +n: Nat
  for p: S.Program
  for +e: D.Schema
  for +s: D.State
  for +ctx: D.Context
  for +args: D.Value
  for credential: String
  for certificate: RO.Program(p)
  {D.authenticate(S.state_execution_trace(S.execute(n, p, e, s, ctx, args)), credential) ==
    D.authenticate(s, credential) : Maybe<&2, D.Context>}
def reads_preserve_fresh_authentication(n, p, e, s, ctx, args, credential, certificate):
  Equal.cong(D.State, Maybe<&2, D.Context>, state => D.authenticate(state, credential),
    S.state_execution_trace(S.execute(n, p, e, s, ctx, args)), s,
    program_preserves_every_prefix(n, p, e, s, ctx, args, certificate))
