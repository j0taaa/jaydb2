# Clauses for the actual prepare/invalidate transition.
import Base
import ../contract/Theorems.bend as T
import ../contract/Logic.bend as L
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/PreparedProtocol.bend as W
import ../contract/PreparedRegistry.bend as G
import ../contract/Requirements.bend as R
import ../contract/Semantics.bend as S
import ../src/Control.bend as C
import ../src/Dispatch.bend as Dispatch
import ../src/Input.bend as Input
import ../src/Codec.bend as Codec
import ../src/Request.bend as Request
import ../src/Gate.bend as Gate
import ../src/Resolve.bend as Resolve
import ./Foundations.bend as F
import ./Ingress.bend as Ingress

def bounded(+schema: D.Schema, -laws: S.Laws, +limits: S.Limits, +instance: String, ok: Bool, +s: D.State, +r: P.Request, -prepare: Bool, -invalidate: Bool,
  -reg: C.Registry, -a: C.Admission, -h: String, +ctx: D.Context,
  +change: C.Change, +receipt: W.Receipt, +bytes: List<&2, U32>,
  auth: T.ControlIdentity(s, r, ctx),
  change_ok: T.ControlChangeAt(prepare, invalidate, S.Configuration{schema, laws, limits, instance}, reg, r, a, h, change, receipt),
  encoded: {W.frame_receipt(receipt) == Some{bytes} : Maybe<&2, List<&2, U32>>},
  fits: {R.fits(R.limit_response(limits), W.receipt_value(receipt)) == ok : Bool}) ->
  T.ControlPlanAt(C.bounded(ok, ctx, change, receipt, bytes), S.Configuration{schema, laws, limits, instance}, s, r, prepare, invalidate, reg, a, h):
  match ok:
    case False{}: Unit{}
    case True{}: L.Both{auth, L.Both{change_ok, L.Both{encoded, fits}}}

def encoded(+schema: D.Schema, -laws: S.Laws, +limits: S.Limits, +instance: String, result: Maybe<&2, List<&2, U32>>, +s: D.State,
  +r: P.Request, -prepare: Bool, -invalidate: Bool, -reg: C.Registry, -a: C.Admission, -h: String,
  +ctx: D.Context, +change: C.Change, +receipt: W.Receipt,
  auth: T.ControlIdentity(s, r, ctx),
  change_ok: T.ControlChangeAt(prepare, invalidate, S.Configuration{schema, laws, limits, instance}, reg, r, a, h, change, receipt),
  exact: {W.frame_receipt(receipt) == result : Maybe<&2, List<&2, U32>>}) ->
  T.ControlPlanAt(C.encoded(limits, instance, result, ctx, change, receipt), S.Configuration{schema, laws, limits, instance}, s, r, prepare, invalidate, reg, a, h):
  match result:
    case None{}: Unit{}
    case Some{+bytes}:
      bounded(schema, laws, limits, instance, R.fits(R.limit_response(limits), W.receipt_value(receipt)), s, r, prepare, invalidate, reg, a, h, ctx, change, receipt, bytes, auth, change_ok, exact, {==})

def receipt(+schema: D.Schema, -laws: S.Laws, +limits: S.Limits, +instance: String, +s: D.State, +r: P.Request, -prepare: Bool, -invalidate: Bool,
  -reg: C.Registry, -a: C.Admission, -h: String, +ctx: D.Context,
  +change: C.Change, +receipt: W.Receipt, auth: T.ControlIdentity(s, r, ctx),
  change_ok: T.ControlChangeAt(prepare, invalidate, S.Configuration{schema, laws, limits, instance}, reg, r, a, h, change, receipt)) ->
  T.ControlPlanAt(C.receipt(limits, instance, ctx, change, receipt), S.Configuration{schema, laws, limits, instance}, s, r, prepare, invalidate, reg, a, h):
  encoded(schema, laws, limits, instance, W.frame_receipt(receipt), s, r, prepare, invalidate, reg, a, h, ctx, change, receipt, auth, change_ok, {==})

def fresh(+schema: D.Schema, -laws: S.Laws, +limits: S.Limits, +instance: String,-invalidate: Bool, ok: Bool, +s: D.State, +r: P.Request,
  +reg: C.Registry, -a: C.Admission, +h: String, +ctx: D.Context,
  auth: T.ControlIdentity(s, r, ctx),
  admitted: {C.admission_matches(a, instance, r) == True{} : Bool},
  +checked: {C.candidate_valid(h) && Bool.not(C.member(h, C.allocated(reg))) == ok : Bool}) ->
  T.ControlPlanAt(C.fresh(limits, instance, ok, ctx, instance, h, r),
    S.Configuration{schema, laws, limits, instance}, s, r, True{}, invalidate, reg, a, h):
  match ok r:
    case False{} _: Unit{}
    case True{} P.Request{credential, +code, args, +proof}:
      receipt(schema, laws, limits, instance, s, P.Request{credential, code, args, proof}, True{}, invalidate, reg, a, h, ctx,
        C.ControlAdd{G.Entry{instance, h, code, proof, False{}, ""}}, W.PreparedReceipt{h},
        auth, L.Both{admitted,
          L.Both{F.and_boolean_left(C.candidate_valid(h), Bool.not(C.member(h, C.allocated(reg))), checked),
            L.Both{F.negation_true(C.member(h, C.allocated(reg)),
              F.and_boolean_right(C.candidate_valid(h), Bool.not(C.member(h, C.allocated(reg))), checked)),
              L.Both{{==}, {==}}}}})

def admitted(+schema: D.Schema, -laws: S.Laws, +limits: S.Limits, +instance: String,-invalidate: Bool, ok: Bool, +s: D.State, +r: P.Request,
  +reg: C.Registry, -a: C.Admission, +h: String, +ctx: D.Context,
  auth: T.ControlIdentity(s, r, ctx),
  checked: {C.admission_matches(a, instance, r) == ok : Bool}) ->
  T.ControlPlanAt(C.admitted(limits, instance, ok, ctx, instance, h, reg, r),
    S.Configuration{schema, laws, limits, instance}, s, r, True{}, invalidate, reg, a, h):
  match ok:
    case False{}: Unit{}
    case True{}:
      fresh(schema, laws, limits, instance, invalidate, C.candidate_valid(h) && Bool.not(C.member(h, C.allocated(reg))), s, r, reg, a, h, ctx, auth, checked, {==})

def found(+schema: D.Schema, -laws: S.Laws, +limits: S.Limits, +instance: String, found: Maybe<&2, G.Entry>, +s: D.State,
  +r: P.Request, -reg: C.Registry, -a: C.Admission, -h: String, +ctx: D.Context,
  auth: T.ControlIdentity(s, r, ctx), empty: {String.eq(Resolve.proof(r), "") == True{} : Bool},
  exact: {G.lookup(instance, Gate.code(r), C.entries(reg)) == found : Maybe<&2, G.Entry>}) ->
  T.ControlPlanAt(C.found(limits, instance, found, ctx, instance, Gate.code(r)), S.Configuration{schema, laws, limits, instance}, s, r, False{}, True{}, reg, a, h):
  match found:
    case None{}: Unit{}
    case Some{entry}:
      receipt(schema, laws, limits, instance, s, r, False{}, True{}, reg, a, h, ctx,
        C.ControlRemove{instance, Gate.code(r)}, W.InvalidatedReceipt{}, auth,
        L.Both{empty, L.Both{(entry, exact), L.Both{{==}, {==}}}})

def invalidating(+schema: D.Schema, -laws: S.Laws, +limits: S.Limits, +instance: String, ok: Bool, +s: D.State, +r: P.Request,
  +reg: C.Registry, -a: C.Admission, -h: String, +ctx: D.Context,
  auth: T.ControlIdentity(s, r, ctx),
  checked: {String.eq(Resolve.proof(r), "") == ok : Bool}) ->
  T.ControlPlanAt(C.invalidating(limits, instance, ok, ctx, instance, reg, Gate.code(r)), S.Configuration{schema, laws, limits, instance}, s, r, False{}, True{}, reg, a, h):
  match ok:
    case False{}: Unit{}
    case True{}:
      found(schema, laws, limits, instance, G.lookup(instance, Gate.code(r), C.entries(reg)), s, r, reg, a, h, ctx, auth, checked, {==})

def tagged(+schema: D.Schema, -laws: S.Laws, +limits: S.Limits, +instance: String, prepare: Bool, invalidate: Bool,
  +s: D.State, +reg: C.Registry, +r: P.Request, +a: C.Admission,
  +h: String, +ctx: D.Context, auth: T.ControlIdentity(s, r, ctx)) ->
  T.ControlPlanAt(C.tagged(limits, instance, prepare, invalidate, ctx, reg, r, a, h), S.Configuration{schema, laws, limits, instance}, s, r, prepare, invalidate, reg, a, h):
  match prepare invalidate:
    case True{} _:
      admitted(schema, laws, limits, instance, invalidate, C.admission_matches(a, instance, r), s, r, reg, a, h, ctx, auth, {==})
    case False{} True{}:
      invalidating(schema, laws, limits, instance, String.eq(Resolve.proof(r), ""), s, r, reg, a, h, ctx, auth, {==})
    case False{} False{}: Unit{}

def authenticated(+schema: D.Schema, -laws: S.Laws, +limits: S.Limits, +instance: String, authentication: Maybe<&2, D.Context>, +tag: U32,
  +s: D.State, +reg: C.Registry, +r: P.Request, +a: C.Admission,
  +h: String, exact: {D.authenticate(s, Gate.credential(r)) == authentication : Maybe<&2, D.Context>}) ->
  T.ControlPlanAt(C.authenticated(limits, instance, authentication, tag, reg, r, a, h),
    S.Configuration{schema, laws, limits, instance}, s, r, U32.is_eq(tag, 3), U32.is_eq(tag, 5), reg, a, h):
  match authentication:
    case None{}: Unit{}
    case Some{+ctx}: tagged(schema, laws, limits, instance, U32.is_eq(tag, 3), U32.is_eq(tag, 5), s, reg, r, a, h, ctx, exact)

def routed(+schema: D.Schema, -laws: S.Laws, +limits: S.Limits, +instance: String,+input: Dispatch.Routed, +reg: C.Registry,
  +a: C.Admission, +h: String) ->
  T.ControlPlan(C.routed(limits, instance, input, reg, a, h), input, S.Configuration{schema, laws, limits, instance}, reg, a, h):
  match input:
    case Dispatch.Routed{+tag, Input.InputReady{+s, +r}}:
      authenticated(schema, laws, limits, instance, D.authenticate(s, Gate.credential(r)), tag, s, reg, r, a, h, {==})
    case Dispatch.Routed{tag, Input.ErrorMessage{status}}: Unit{}
    case Dispatch.Routed{tag, Input.ErrorTransport{}}: Unit{}

def preserved(plan: C.Plan, -c: S.Configuration, +root: D.State, +last: List<&2, U32>,
  +reg: C.Registry, -body: List<&2, U32>, -a: C.Admission, -h: String) ->
  T.ControlResult(T.ControlPreserved{}, plan, c, root, last, reg, body, a, h, C.finish(plan, root, last, reg)):
  match plan:
    case C.ControlDenied{status}: L.Both{{==}, {==}}
    case C.ControlReady{ctx, change, receipt, bytes}: L.Both{{==}, {==}}

def delta(+plan: C.Plan, -c: S.Configuration, +root: D.State, +last: List<&2, U32>,
  +reg: C.Registry, -body: List<&2, U32>, -a: C.Admission, -h: String) ->
  T.ControlResult(T.ControlDelta{}, plan, c, root, last, reg, body, a, h, C.finish(plan, root, last, reg)):
  match plan:
    case C.ControlDenied{status}: L.Both{{==}, {==}}
    case C.ControlReady{ctx, change, receipt, bytes}: L.Both{{==}, {==}}

def rooted_pre(+pre: Input.PreAuthentication, +tag: U32, -s: D.State,
  rooted: Ingress.Received(pre, s)) -> T.ControlRooted(Dispatch.Routed{tag, pre}, s):
  match pre:
    case Input.InputReady{state, r}: rooted
    case Input.ErrorMessage{status}: Unit{}
    case Input.ErrorTransport{}: Unit{}

def rooted_limit(limit: Maybe<&2, B.Number64>, +tag: U32, +body: List<&2, U32>, +s: D.State) ->
  T.ControlRooted(Dispatch.Routed{tag, Input.read_message(limit, body, s)}, s):
  match limit:
    case None{}: Unit{}
    case Some{+n}:
      rooted_pre(Input.read_message(Some{n}, body, s), tag, s,
        Ingress.received_measure(B.nat64(B.length(body)), body, n, s))

def rooted_envelope(e: Dispatch.Envelope, +s: D.State, +limit: Maybe<&2, B.Number64>) ->
  T.ControlRooted(Dispatch.received_envelope(e, s, limit), s):
  match e:
    case Dispatch.Invalid{}: Unit{}
    case Dispatch.Envelope{+tag, +body}: rooted_limit(limit, tag, body, s)

def rooted_fits(fits: Bool, +body: List<&2, U32>, +s: D.State, +limit: Maybe<&2, B.Number64>) ->
  T.ControlRooted(Dispatch.received_fits(fits, body, s, limit), s):
  match fits:
    case False{}: Unit{}
    case True{}: rooted_envelope(Dispatch.envelope(body), s, limit)

def measured_plan(plan: C.Plan, -c: S.Configuration, -body: List<&2, U32>,
  fits: {Nat.is_le(B.length(body), R.limit_message(S.limits(c))) == True{} : Bool}) ->
  T.ControlMeasured(plan, c, body):
  match plan:
    case C.ControlDenied{status}: Unit{}
    case C.ControlReady{ctx, change, receipt, bytes}: fits

def measured(+schema: D.Schema, -laws: S.Laws, +limits: S.Limits, +instance: String, fits: Bool, +body: List<&2, U32>, +s: D.State,
  +reg: C.Registry, +a: C.Admission, +h: String,
  checked: {Nat.is_le(B.length(body), R.limit_message(limits)) == fits : Bool}) ->
  T.ControlMeasured(C.routed(limits, instance, Dispatch.received_fits(fits, body, s,
    B.nat64(R.limit_message(limits))), reg, a, h), S.Configuration{schema, laws, limits, instance}, body):
  match fits:
    case False{}: Unit{}
    case True{}:
      measured_plan(C.routed(limits, instance, Dispatch.received_fits(True{}, body, s,
        B.nat64(R.limit_message(limits))), reg, a, h), S.Configuration{schema, laws, limits, instance}, body, checked)

def clause(+schema: D.Schema, -laws: S.Laws, +limits: S.Limits, +instance: String, k: T.ControlClause, +root: D.State, +last: List<&2, U32>,
  +reg: C.Registry, +body: List<&2, U32>, +a: C.Admission, +h: String) ->
  T.ControlAt(S.Configuration{schema, laws, limits, instance}, k, root, last, reg, body, a, h):
  match k:
    case T.ControlPreserved{}: preserved(C.plan(S.Configuration{schema, S.NoneLaw{}, limits, instance}, root, reg, body, a, h), S.Configuration{schema, laws, limits, instance}, root, last, reg, body, a, h)
    case T.ControlDelta{}: delta(C.plan(S.Configuration{schema, S.NoneLaw{}, limits, instance}, root, reg, body, a, h), S.Configuration{schema, laws, limits, instance}, root, last, reg, body, a, h)
    case T.ControlChecked{}: routed(schema, laws, limits, instance, Dispatch.received(limits, body, root), reg, a, h)
    case T.ControlReception{}:
      L.Both{rooted_fits(Nat.is_le(B.length(body), R.limit_message(limits)), body, root,
        B.nat64(R.limit_message(limits))),
        measured(schema, laws, limits, instance, Nat.is_le(B.length(body), R.limit_message(limits)), body, root, reg, a, h, {==})}

def configuration(c: S.Configuration, k: T.ControlClause, +root: D.State, +last: List<&2, U32>,
  +reg: C.Registry, +body: List<&2, U32>, +a: C.Admission, +h: String) ->
  T.ControlAt(c, k, root, last, reg, body, a, h):
  match c:
    case S.Configuration{+schema, laws, +limits, +instance}:
      clause(schema, laws, limits, instance, k, root, last, reg, body, a, h)

def control_theorem() -> T.ControlTheorem():
  k => c => root => last => registry => body => a => h => configuration(c, k, root, last, registry, body, a, h)
