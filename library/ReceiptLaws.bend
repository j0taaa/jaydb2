# Administrator-frozen protocol refinement template. Not a source allowlist.
# Prefixes include reads that fail or precede refusal; success must complete.
import Base
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/Requirements.bend as R
import ../contract/Logic.bend as L

type Both<-P: Data, -Q: Data> is Data:
  Both{left: P, right: Q}

def technical(e: D.Schema, lim: S.Limits) -> S.Configuration:
  S.Configuration{e, S.NoneLaw{}, lim, ""}

def At(+p: S.Trace, w: D.State, ts: List<&2, S.OperationEvent>) -> Data:
  Both<{S.state_execution_trace(p) == w : D.State},
    {S.events_execution_trace(p) == ts : List<&2, S.OperationEvent>}>

def Finished(p: S.Trace, v: D.Value) -> Data:
  match p:
    case S.Prefix{w, ts}: Empty
    case S.Final{w, ts, result}: {result == S.Response{S.Success{}, v} : S.Response}

def Success(p: S.Trace, +e: D.Schema, +lim: S.Limits, r: S.Response) -> Data:
  match r:
    case S.Response{S.Success{}, v}: Finished(p, v)
    case _: Unit

def Reachable(~ref: S.Program, +e: D.Schema, +s: D.State, +ctx: D.Context,
  +args: D.Value, +w: D.State, +ts: List<&2, S.OperationEvent>) -> Data:
  Sigma<&2, &2, Nat, n => At(S.execute(n, ref, e, s, ctx, args), w, ts)>

def Closed(~ref: S.Program, +e: D.Schema, +lim: S.Limits, +s: D.State,
  +ctx: D.Context, +args: D.Value, +w: D.State,
  +ts: List<&2, S.OperationEvent>, +r: S.Response) -> Data:
  Sigma<&2, &2, Nat, n => Both<At(S.execute(n, ref, e, s, ctx, args), w, ts),
    Success(S.execute(n, ref, e, s, ctx, args), e, lim, r)>>

# Ghost history, erased by Bend. No runtime journal or retained public log.
# A stable state must arise from the frozen seed by complete protocol calls.
type Call is Data:
  Call{context: D.Context, arguments: D.Value, depth: Nat}

def advance(p: S.Trace, e: D.Schema, lim: S.Limits, initial: D.State) -> D.State:
  match p:
    case S.Prefix{w, ts}: initial
    case S.Final{+w, ts, r}: S.publish(R.finalize(r, technical(e, lim), w), initial, w)

def replay(~ref: S.Program, +e: D.Schema, +lim: S.Limits, +seed: D.State,
  calls: List<&2, Call>) -> D.State:
  match calls:
    case Nil{}: seed
    case Con{Call{ctx, args, n}, rest}:
      +initial = replay(~ref, e, lim, seed, rest)
      advance(S.execute(n, ref, e, initial, ctx, args), e, lim, initial)

def State(~ref: S.Program, ~origin: D.State -> Data, +e: D.Schema, +lim: S.Limits, +s: D.State) -> Data:
  Sigma<&2, &2, D.State, seed => Sigma<&2, &2, List<&2, Call>, calls =>
    Both<origin(seed), {replay(~ref, e, lim, seed, calls) == s : D.State}>>>

# This is a semantic protocol template. The administrator freezes ref and seed.
def Rule(~ref: S.Program, ~origin: D.State -> Data, +e: D.Schema, +lim: S.Limits, h: S.Situation) -> Data:
  match h:
    case S.Stable{s}: State(~ref, ~origin, e, lim, s)
    case S.Executing{s, ctx, code, args, w, ts}:
      Both<State(~ref, ~origin, e, lim, s), Reachable(~ref, e, s, ctx, args, w, ts)>
    case S.Closed{s, ctx, code, args, w, ts, r}:
      Both<State(~ref, ~origin, e, lim, s), Closed(~ref, e, lim, s, ctx, args, w, ts, r)>

# A successful replay step is constructive evidence for the next stable state.
def extend(~ref: S.Program, ~origin: D.State -> Data, +e: D.Schema, +lim: S.Limits,
  +s: D.State, +ctx: D.Context, +args: D.Value, +n: Nat,
  h: State(~ref, ~origin, e, lim, s)) ->
  State(~ref, ~origin, e, lim, advance(S.execute(n, ref, e, s, ctx, args), e, lim, s)):
  match h:
    case (seed, calls, Both{base, eq}):
      (seed, Call{ctx, args, n} <> calls, Both{base,
        Equal.cong(D.State, D.State, +initial => advance(S.execute(n, ref, e, initial, ctx, args), e, lim, initial),
          replay(~ref, e, lim, seed, calls), s, eq)})


def same_at(p: S.Trace) -> At(p, S.state_execution_trace(p), S.events_execution_trace(p)):
  Both{{==}, {==}}

def failure(p: S.Trace, e: D.Schema, lim: S.Limits) ->
  Success(p, e, lim, S.response_error(S.Failure{})):
  Unit{}

def success_cases(ok: Bool, fits: Bool, +payload: Bool, +size: Bool,
  +e: D.Schema, +lim: S.Limits, +w: D.State, +ts: List<&2, S.OperationEvent>, +v: D.Value) ->
  Success(S.Final{w, ts, S.Response{S.Success{}, v}}, e, lim,
    R.state_technical_cases(ok, fits, R.response_technique_cases(payload, size, S.Response{S.Success{}, v}))):
  match ok fits payload size:
    case True{} True{} True{} True{}: {==}
    case True{} True{} False{} _: Unit{}
    case True{} True{} True{} False{}: Unit{}
    case False{} _ _ _: Unit{}
    case True{} False{} _ _: Unit{}

def refusal_cases(ok: Bool, fits: Bool, +e: D.Schema, +lim: S.Limits,
  +w: D.State, +ts: List<&2, S.OperationEvent>, +v: D.Value) ->
  Success(S.Final{w, ts, S.Response{S.Refusal{}, v}}, e, lim,
    R.response_technique_cases(ok, fits, S.Response{S.Refusal{}, v})):
  match ok fits:
    case False{} _: Unit{}
    case True{} False{}: Unit{}
    case True{} True{}: Unit{}

def finalized(+e: D.Schema, +lim: S.Limits, +w: D.State,
  +ts: List<&2, S.OperationEvent>, r: S.Response) ->
  Success(S.Final{w, ts, r}, e, lim, R.finalize(r, technical(e, lim), w)):
  match r:
    case S.Response{S.Success{}, +v}:
      success_cases(D.structure(e, w), R.fits(R.limit_state(lim), D.state_value(w)),
        D.value_valid(v), R.fits(R.limit_response(lim), S.response_value(S.Response{S.Success{}, v})), e, lim, w, ts, v)
    case S.Response{S.Refusal{}, +v}:
      refusal_cases(D.value_valid(v), R.fits(R.limit_response(lim), S.response_value(S.Response{S.Refusal{}, v})), e, lim, w, ts, v)
    case S.Response{S.Input{}, v}: Unit{}
    case S.Response{S.Authentication{}, v}: Unit{}
    case S.Response{S.Certificate{}, v}: Unit{}
    case S.Response{S.DataError{}, v}: Unit{}
    case S.Response{S.Limit{}, v}: Unit{}
    case S.Response{S.Failure{}, v}: Unit{}

# Technical finalization does not inspect laws or environment. Explicitly bridge
# configurations rather than assuming definitional reduction under an unknown r.
def finalize_equivalent(~laws: S.Laws, r: S.Response, +e: D.Schema, +lim: S.Limits,
  environment: String, +w: D.State) ->
  {R.finalize(r, S.Configuration{e, laws, lim, environment}, w) == R.finalize(r, technical(e, lim), w) : S.Response}:
  match r:
    case S.Response{S.Success{}, v}: {==}
    case S.Response{S.Refusal{}, v}: {==}
    case S.Response{S.Input{}, v}: {==}
    case S.Response{S.Authentication{}, v}: {==}
    case S.Response{S.Certificate{}, v}: {==}
    case S.Response{S.DataError{}, v}: {==}
    case S.Response{S.Limit{}, v}: {==}
    case S.Response{S.Failure{}, v}: {==}
