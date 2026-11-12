# State-indexed weakest preconditions over the REAL Data.operate result.
# Every access needs its permission; a successful finish needs the exact
# directory law of the CURRENT working state. Prefixes may be stale.
import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Requirements.bend as R
import ./Logic.bend as L
import ./Termination.bend as T
import ./ValidationFinal.bend as V
import ./Policy.bend as P
import ./Ownership.bend as O
import ./MutationStateShapeProofs.bend as Shape
import ./ReadOperationProofs.bend as RO
import ./ValueScalarProofs.bend as Pair

def Step(res: D.ResultOp, +s: D.State, post: @r: S.Return -> @w: D.State -> Type) -> Type:
  match res:
    case D.FailureData{}: Unit
    case D.Observed{obs}: post(S.Datum{obs}, s)
    case D.Changed{w}: post(S.UnitValue{}, w)

# The depth bounds only how far this judgment is unfolded; the certificate
# supplies it at the observation depth of every trace (see safe).
def Judge(a: S.Action, d: Nat, +e: D.Schema, +ctx: D.Context, +s: D.State) -> Type:
  match a:
    case S.Finish{v}: P.Directory(s)
    case S.Refuse{v}: Unit
    case S.Access{+op, k}:
      match d:
        case Zero{}: Unit
        case Succ{m}: L.E<P.Allowed(ctx, op), Step(D.operate(e, s, op), s, r => w => Judge(k(r), m, e, ctx, w))>

def Safe(d: Nat, +e: D.Schema, +ctx: D.Context, +s: D.State, a: S.Action) -> Type:
  Judge(a, d, e, ctx, s)

def access(d: Nat, +e: D.Schema, +ctx: D.Context, +s: D.State, +op: D.Operation, -k: S.Return -> S.Action,
  p: P.Allowed(ctx, op), h: @m: Nat -> Step(D.operate(e, s, op), s, r => w => Safe(m, e, ctx, w, k(r)))) ->
  Safe(d, e, ctx, s, S.Access{op, k}):
  match d:
    case Zero{}: Unit{}
    case Succ{m}: L.Both{p, h(m)}

def shaped(res: D.ResultOp, +m: Nat, +e: D.Schema, +ctx: D.Context, +s: D.State, +c: D.Collection,
  +t: Shape.Transform, -k: S.Return -> S.Action, sh: Shape.Shape(s, c, t, res),
  h: @rows: List<&2, D.Row> -> {D.rows_collection(c, s) == Some{rows} : Maybe<&2, List<&2, D.Row>>} ->
    Safe(m, e, ctx, D.swap_collection(c, s, Shape.apply(t, rows)), k(S.UnitValue{}))) ->
  Step(res, s, r => w => Safe(m, e, ctx, w, k(r))):
  match res:
    case D.FailureData{}: Unit{}
    case D.Observed{o}: O.impossible(Safe(m, e, ctx, s, k(S.Datum{o})), sh)
    case D.Changed{+w}:
      match sh:
        case (+rows, Pair.Both{found, same}):
          %Equal.sym(D.State, w, D.swap_collection(c, s, Shape.apply(t, rows)), same) : Safe(m, e, ctx, _, k(S.UnitValue{}))
          h(rows, found)

# A row write or removal: the continuation sees the exact actual working state.
def written(+m: Nat, +e: D.Schema, +ctx: D.Context, +s: D.State, +c: D.Collection, +t: Shape.Transform,
  -k: S.Return -> S.Action,
  h: @rows: List<&2, D.Row> -> {D.rows_collection(c, s) == Some{rows} : Maybe<&2, List<&2, D.Row>>} ->
    Safe(m, e, ctx, D.swap_collection(c, s, Shape.apply(t, rows)), k(S.UnitValue{}))) ->
  Step(D.operate(e, s, Shape.operation(c, t)), s, r => w => Safe(m, e, ctx, w, k(r))):
  shaped(D.operate(e, s, Shape.operation(c, t)), m, e, ctx, s, c, t, k,
    Shape.actual_ordinary_row_transform_has_complete_input_state_shape_for_every_input(e, s, c, t), h)

def observed(res: D.ResultOp, +m: Nat, +e: D.Schema, +ctx: D.Context, +s: D.State, +kind: RO.ReadKind,
  -k: S.Return -> S.Action, sh: RO.ResultKind(kind, res),
  h: @o: D.Observation -> Safe(m, e, ctx, s, k(S.Datum{o}))) -> Step(res, s, r => w => Safe(m, e, ctx, w, k(r))):
  match res:
    case D.FailureData{}: Unit{}
    case D.Observed{+o}: h(o)
    case D.Changed{w}: O.impossible(Safe(m, e, ctx, w, k(S.UnitValue{})), sh)

# A read never changes the working state.
def reading(+m: Nat, +e: D.Schema, +ctx: D.Context, +s: D.State, +kind: RO.ReadKind, +c: D.Collection,
  +key: String, +column: String, -k: S.Return -> S.Action,
  h: @o: D.Observation -> Safe(m, e, ctx, s, k(S.Datum{o}))) ->
  Step(D.operate(e, s, RO.operation(kind, c, key, column)), s, r => w => Safe(m, e, ctx, w, k(r))):
  observed(D.operate(e, s, RO.operation(kind, c, key, column)), m, e, ctx, s, kind, k,
    RO.real_named_read_operations_have_only_the_expected_observation_or_data_failure(kind, e, s, c, key, column), h)

def Good(+ctx: D.Context, +s: D.State, ts: List<&2, S.OperationEvent>) -> Data:
  P.Both<P.Owners(s), P.Both<{D.context_present(s, ctx) == True{} : Bool}, P.AllAllowed(ctx, ts)>>

def Done(r: S.Response, +w: D.State) -> Type:
  match r:
    case S.Response{S.Success{}, v}: P.Directory(w)
    case S.Response{S.Refusal{}, v}: Unit
    case S.Response{S.Input{}, v}: Unit
    case S.Response{S.Authentication{}, v}: Unit
    case S.Response{S.Certificate{}, v}: Unit
    case S.Response{S.DataError{}, v}: Unit
    case S.Response{S.Limit{}, v}: Unit
    case S.Response{S.Failure{}, v}: Unit

def Terminal(p: S.Trace) -> Type:
  match p:
    case S.Prefix{w, ts}: Unit
    case S.Final{+w, ts, r}: Done(r, w)

def Path(+ctx: D.Context, +p: S.Trace) -> Type:
  L.E<Good(ctx, S.state_execution_trace(p), S.events_execution_trace(p)), Terminal(p)>

def rewind(-ctx: D.Context, -a: S.Trace, -b: S.Trace, eq: {a == b : S.Trace}, h: Path(ctx, b)) -> Path(ctx, a):
  %Equal.sym(S.Trace, a, b, eq) : Path(ctx, _)
  h

def append(+ctx: D.Context, ts: List<&2, S.OperationEvent>, +op: D.Operation, +ef: S.Effect,
  h: P.AllAllowed(ctx, ts), p: P.Allowed(ctx, op)) -> P.AllAllowed(ctx, S.append(ts, S.OperationEvent{op, ef})):
  match ts h:
    case Nil{} Unit{}: P.Both{p, Unit{}}
    case Con{S.OperationEvent{o, effect}, tail} P.Both{hp, ht}: P.Both{hp, append(ctx, tail, op, ef, ht, p)}

def result(res: D.ResultOp, +n: Nat, +ctx: D.Context, +e: D.Schema, +s: D.State, +ts: List<&2, S.OperationEvent>,
  +op: D.Operation, -k: S.Return -> S.Action, +good: Good(ctx, s, ts), +p: P.Allowed(ctx, op),
  post: O.Preserves(ctx, res), h: Step(res, s, r => w => Safe(Succ{n}, e, ctx, w, k(r))),
  rec: @r: S.Return -> @w: D.State -> @events: List<&2, S.OperationEvent> -> Good(ctx, w, events) ->
    Safe(Succ{n}, e, ctx, w, k(r)) -> Path(ctx, T.observe(n, k(r), e, w, events))) ->
  Path(ctx, S.resume_execution_trace(n, S.apply(res, s, op, k), e, ts)):
  match res:
    case D.FailureData{}:
      P.Both{owners, P.Both{present, hist}} = good
      rewind(ctx, S.resume_execution_trace(n, S.OperationFailed{s, S.OperationEvent{op, S.ErrorOfData{}}}, e, ts),
        S.Final{s, S.append(ts, S.OperationEvent{op, S.ErrorOfData{}}), S.response_error(S.DataError{})},
        T.failure_of_operation(n, s, S.OperationEvent{op, S.ErrorOfData{}}, e, ts),
        L.Both{P.Both{owners, P.Both{present, append(ctx, ts, op, S.ErrorOfData{}, hist, p)}}, Unit{}})
    case D.Observed{+obs}:
      P.Both{owners, P.Both{present, hist}} = good
      rewind(ctx, S.resume_execution_trace(n, S.Continue{s, k(S.Datum{obs}), S.OperationEvent{op, S.Reading{obs}}}, e, ts),
        T.observe(n, k(S.Datum{obs}), e, s, S.append(ts, S.OperationEvent{op, S.Reading{obs}})),
        T.continuation(n, s, k(S.Datum{obs}), S.OperationEvent{op, S.Reading{obs}}, e, ts),
        rec(S.Datum{obs}, s, S.append(ts, S.OperationEvent{op, S.Reading{obs}}),
          P.Both{owners, P.Both{present, append(ctx, ts, op, S.Reading{obs}, hist, p)}}, h))
    case D.Changed{+w}:
      P.Both{owners, P.Both{present, hist}} = good
      L.Both{new, authenticated} = post
      rewind(ctx, S.resume_execution_trace(n, S.Continue{w, k(S.UnitValue{}), S.OperationEvent{op, S.Write{}}}, e, ts),
        T.observe(n, k(S.UnitValue{}), e, w, S.append(ts, S.OperationEvent{op, S.Write{}})),
        T.continuation(n, w, k(S.UnitValue{}), S.OperationEvent{op, S.Write{}}, e, ts),
        rec(S.UnitValue{}, w, S.append(ts, S.OperationEvent{op, S.Write{}}),
          P.Both{new, P.Both{authenticated, append(ctx, ts, op, S.Write{}, hist, p)}}, h))

# Observation depth n is covered by the judgment unfolded to depth n + 1.
def safe(n: Nat, a: S.Action, +ctx: D.Context, +e: D.Schema, +s: D.State, +ts: List<&2, S.OperationEvent>,
  h: Safe(Succ{n}, e, ctx, s, a), +good: Good(ctx, s, ts)) -> Path(ctx, T.observe(n, a, e, s, ts)):
  match n h:
    case Zero{} h: L.Both{good, Unit{}}
    case Succ{+rest} h:
      match a h:
        case S.Finish{v} dir:
          rewind(ctx, S.resume_execution_trace(rest, S.Stopped{s, S.Response{S.Success{}, v}}, e, ts),
            S.Final{s, ts, S.Response{S.Success{}, v}}, T.stopped(rest, s, S.Response{S.Success{}, v}, e, ts), L.Both{good, dir})
        case S.Refuse{v} Unit{}:
          rewind(ctx, S.resume_execution_trace(rest, S.Stopped{s, S.Response{S.Refusal{}, v}}, e, ts),
            S.Final{s, ts, S.Response{S.Refusal{}, v}}, T.stopped(rest, s, S.Response{S.Refusal{}, v}, e, ts), L.Both{good, Unit{}})
        case S.Access{+op, k} L.Both{+p, step}:
          P.Both{+owners, P.Both{+aut, +hist}} = good
          result(D.operate(e, s, op), rest, ctx, e, s, ts, op, k, P.Both{owners, P.Both{aut, hist}}, p,
            O.operation_preserves(e, s, ctx, op, owners, aut, p), step,
            +r => w => events => g => hh => safe(rest, k(r), ctx, e, w, events, hh, g))

def configuration(e: D.Schema, lim: S.Limits, amb: String) -> S.Configuration:
  P.config(e, lim, amb)

def prefix(-e: D.Schema, -lim: S.Limits, -amb: String, -s: D.State, -ctx: D.Context, -code: String,
  -args: D.Value, -w: D.State, -ts: List<&2, S.OperationEvent>, +owners: P.Owners(w), +hist: P.AllAllowed(ctx, ts)) ->
  R.SafetyPrefix(configuration(e, lim, amb), s, ctx, code, args, w, ts):
  L.Both{L.Both{P.Both{owners, hist}, L.Both{Unit{}, Unit{}}}, L.Both{P.Both{owners, hist}, L.Both{Unit{}, Unit{}}}}

def finalize(r: S.Response, +e: D.Schema, +lim: S.Limits, +amb: String, +w: D.State, +owners: P.Owners(w), done: Done(r, w)) ->
  R.PublicationValid(R.finalize(r, configuration(e, lim, amb), w), configuration(e, lim, amb), w):
  match r done:
    case S.Response{S.Success{}, +v} dir:
      V.state_validated(D.structure(e, w), R.fits(R.limit_state(lim), D.state_value(w)),
        e, P.laws(), lim, amb, w, v, D.value_valid(v),
        R.fits(R.limit_response(lim), S.response_value(S.Response{S.Success{}, v})), {==}, {==},
        L.Both{owners, L.Both{dir, Unit{}}})
    case S.Response{S.Refusal{}, +v} Unit{}:
      V.refusal_validated(D.value_valid(v), R.fits(R.limit_response(lim), S.response_value(S.Response{S.Refusal{}, v})), configuration(e, lim, amb), w, v)
    case S.Response{S.Input{}, v} Unit{}: Unit{}
    case S.Response{S.Authentication{}, v} Unit{}: Unit{}
    case S.Response{S.Certificate{}, v} Unit{}: Unit{}
    case S.Response{S.DataError{}, v} Unit{}: Unit{}
    case S.Response{S.Limit{}, v} Unit{}: Unit{}
    case S.Response{S.Failure{}, v} Unit{}: Unit{}

def execution_trace(p: S.Trace, +e: D.Schema, +lim: S.Limits, +amb: String, -s: D.State, -ctx: D.Context,
  -code: String, -args: D.Value, h: Path(ctx, p)) -> R.SafetyTrace(p, configuration(e, lim, amb), s, ctx, code, args):
  match p h:
    case S.Prefix{w, ts} L.Both{P.Both{owners, P.Both{aut, hist}}, Unit{}}:
      prefix(e, lim, amb, s, ctx, code, args, w, ts, owners, hist)
    case S.Final{+w, ts, +r} L.Both{P.Both{+owners, P.Both{aut, +hist}}, done}:
      L.Both{prefix(e, lim, amb, s, ctx, code, args, w, ts, owners, hist),
        L.Both{L.Both{P.Both{owners, hist}, L.Both{Unit{}, Unit{}}}, finalize(r, e, lim, amb, w, owners, done)}}
