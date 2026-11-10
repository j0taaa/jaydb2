# State invariant by induction on actual N.conclude results.
# Includes stores followed by process loss, without requiring delivered response.
import Base
import ../contract/Data.bend as D
import ../contract/RequestFacts.bend as I
import ../contract/Logic.bend as L
import ../contract/Protocol.bend as P
import ../contract/Requirements.bend as R
import ../contract/Semantics.bend as S
import ../src/Core.bend as N
import ./Publication.bend as U
import ./Preparation.bend as Q

# Metadata without private state in client source. History is semantic,
# not a new log required from the server.
type Record is Data:
  Record{request: P.Request, context: D.Context, steps: Nat,
    working: D.State, events: List<&2, S.OperationEvent>, proposal: S.Response,
    prepared: N.Prepared}

def next(s: D.State, r: Record) -> D.State:
  match r:
    case Record{req, ctx, n, w, ts, prop, prepared}:
      U.published(N.conclude(prepared, s))

def state(rs: List<&2, Record>, s: D.State) -> D.State:
  match rs:
    case Nil{}: s
    case Con{h, t}: state(t, next(s, h))

# Origin stores the certificate and function EQUALITIES, not Law6 conclusions.
def Origin(-c: S.Configuration, -s: D.State, r: Record) -> Type:
  match r:
    case Record{req, ctx, n, w, ts, prop, prepared}:
      &p: S.Program ->
        L.E<R.Certifies(c, I.code(req), p, ctx, I.arguments(req)),
          L.E<{D.authenticate(s, I.credential(req)) == Some{ctx} : Maybe<&2, D.Context>},
            L.E<{N.traverse(n, N.start(p, ctx, I.arguments(req), s), S.schema(c)) ==
              S.Final{w, ts, prop} : S.Trace},
              {N.prepare(N.Stopped{w, ts, prop}, c) == Some{prepared} : Maybe<&2, N.Prepared>}>>>

def Sources(-c: S.Configuration, rs: List<&2, Record>, +s: D.State) -> Type:
  match rs:
    case Nil{}: Unit
    case Con{+h, t}: L.E<Origin(c, s, h), Sources(c, t, next(s, h))>

law step_preserves_validity:
  for ~c: S.Configuration
  for +s: D.State
  for +r: Record
  for valid: R.Valid(c, s)
  for origin: Origin(c, s, r)
  R.Valid(c, next(s, r))
def step_preserves_validity(c, s, r, valid, origin):
  match r:
    case Record{req, ctx, n, w, ts, prop, prepared}:
      match origin:
        case (p, L.Both{certificate, L.Both{aut, L.Both{obtained, preparation_result}}}):
          U.conclusion_of_preparation_certified_and_is_valid(c, I.code(req), p, ctx, I.arguments(req),
            certificate, s, valid, I.credential(req), aut, n, w, ts, prop, obtained, prepared,
            Q.prepare_preserves_response_state_events_and_bytes(N.Stopped{w, ts, prop}, c, prepared, preparation_result))

law history_preserves_validity:
  for ~c: S.Configuration
  for rs: List<&2, Record>
  for +s: D.State
  for initial: R.Valid(c, s)
  for sources: Sources(c, rs, s)
  R.Valid(c, state(rs, s))
def history_preserves_validity(c, rs, s, initial, sources):
  match rs sources:
    case Nil{} _: initial
    case Con{+h, t} L.Both{origin, rest}:
      history_preserves_validity(c, t, next(s, h),
        step_preserves_validity(c, s, h, initial, origin), rest)
