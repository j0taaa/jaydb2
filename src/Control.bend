# Pure prepared control transition. Admission is an exact T1 result, never a
# client Boolean. The host supplies it only after both official checks succeed.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/PreparedProtocol.bend as W
import ../contract/PreparedRegistry.bend as G
import ../contract/PreparedHandles.bend as Handles
import ../contract/Requirements.bend as R
import ../contract/Semantics.bend as S
import ./Dispatch.bend as Dispatch
import ./Input.bend as Input
import ./Gate.bend as Gate
import ./Resolve.bend as Resolve

type Registry is Data:
  ControlRegistry{entries: List<&2, G.Entry>, used: List<&2, String>}

type Admission is Data:
  ControlUnaccepted{}
  ControlUniversal{instance: String, code: String, proof: String}

type Change is Data:
  ControlAdd{entry: G.Entry}
  ControlRemove{instance: String, handle: String}

type Plan is Data:
  ControlDenied{status: S.Status}
  ControlReady{context: D.Context, change: Change, receipt: W.Receipt, bytes: List<&2, U32>}

# Metadata is distinct from a transaction response. Neither updates the last
# published root/response pair, including on successful invalidation.
type Outcome is Data:
  ControlTransaction{response: S.Response}
  ControlMetadata{receipt: W.Receipt, bytes: List<&2, U32>}

type Transition is Data:
  ControlResult{root: D.State, last: List<&2, U32>, registry: Registry, outcome: Outcome}

def entries(registry: Registry) -> List<&2, G.Entry>:
  ControlRegistry{es, used} = registry
  es

def used(registry: Registry) -> List<&2, String>:
  ControlRegistry{es, used} = registry
  used

def keys(es: List<&2, G.Entry>, history: List<&2, String>) -> List<&2, String>:
  match es:
    case Nil{}: history
    case Con{G.Entry{i, h, c, p, ro, seal}, rest}: Con{h, keys(rest, history)}

def allocated(reg: Registry) -> List<&2, String>:
  ControlRegistry{es, history} = reg
  keys(es, history)

def member(+h: String, keys: List<&2, String>) -> Bool:
  match keys:
    case Nil{}: False{}
    case Con{k, rest}: String.eq(h, k) || member(h, rest)

def candidate_valid(+h: String) -> Bool:
  Nat.is_eq(String.length(h), 64n) && Handles.hex_text(h)

def admission_tuple(a: Admission, +i: String, code: String, proof: String) -> Bool:
  match a:
    case ControlUniversal{ai, ac, ap}: String.eq(ai, i) && String.eq(ac, code) && String.eq(ap, proof)
    case ControlUnaccepted{}: False{}

def admission_matches(a: Admission, +i: String, r: P.Request) -> Bool:
  P.Request{credential, code, args, proof} = r
  admission_tuple(a, i, code, proof)


def remove_if(same: Bool, entry: G.Entry, rest: List<&2, G.Entry>) -> List<&2, G.Entry>:
  match same:
    case True{}: rest
    case False{}: Con{entry, rest}

def remove(+i: String, +h: String, es: List<&2, G.Entry>) -> List<&2, G.Entry>:
  match es:
    case Nil{}: Nil{}
    case Con{+e, rest}: remove_if(G.matches(i, h, e), e, remove(i, h, rest))

def apply(change: Change, registry: Registry) -> Registry:
  match change registry:
    case ControlAdd{G.Entry{i, +h, c, p, ro, seal}} ControlRegistry{es, history}:
      ControlRegistry{Con{G.Entry{i, h, c, p, ro, seal}, es}, Con{h, history}}
    case ControlRemove{i, h} ControlRegistry{es, history}: ControlRegistry{remove(i, h, es), history}

# The ONLY Ready constructor is after exact encoding and the body-size bound.
# Applying its delta happens later, in finish; encoding failure cannot mutate.
def bounded(ok: Bool, ctx: D.Context, change: Change, receipt: W.Receipt,
  bytes: List<&2, U32>) -> Plan:
  match ok:
    case False{}: ControlDenied{S.Limit{}}
    case True{}: ControlReady{ctx, change, receipt, bytes}

def encoded(+limits: S.Limits, +instance: String, encoded: Maybe<&2, List<&2, U32>>,
  ctx: D.Context, change: Change, +receipt: W.Receipt) -> Plan:
  match encoded:
    case None{}: ControlDenied{S.Limit{}}
    case Some{bytes}:
      bounded(R.fits(R.limit_response(limits), W.receipt_value(receipt)), ctx, change, receipt, bytes)

def receipt(+limits: S.Limits, +instance: String, ctx: D.Context, change: Change, +receipt: W.Receipt) -> Plan:
  encoded(limits, instance, W.frame_receipt(receipt), ctx, change, receipt)

def fresh(+limits: S.Limits, +instance: String, ok: Bool, ctx: D.Context, +i: String, +h: String, r: P.Request) -> Plan:
  match ok r:
    case False{} _: ControlDenied{S.Failure{}}
    case True{} P.Request{credential, code, args, proof}:
      receipt(limits, instance, ctx, ControlAdd{G.Entry{i, h, code, proof, False{}, ""}}, W.PreparedReceipt{h})

def admitted(+limits: S.Limits, +instance: String, ok: Bool, ctx: D.Context, +i: String,
  +h: String, registry: Registry, r: P.Request) -> Plan:
  match ok:
    case False{}: ControlDenied{S.Certificate{}}
    case True{}:
      fresh(limits, instance, candidate_valid(h) && Bool.not(member(h, allocated(registry))), ctx, i, h, r)

def found(+limits: S.Limits, +instance: String, found: Maybe<&2, G.Entry>, ctx: D.Context,
  i: String, h: String) -> Plan:
  match found:
    case None{}: ControlDenied{S.Failure{}}
    case Some{entry}: receipt(limits, instance, ctx, ControlRemove{i, h}, W.InvalidatedReceipt{})

def invalidating(+limits: S.Limits, +instance: String, empty: Bool, ctx: D.Context,
  +i: String, registry: Registry, +h: String) -> Plan:
  match empty:
    case False{}: ControlDenied{S.Input{}}
    case True{}: found(limits, instance, G.lookup(i, h, entries(registry)), ctx, i, h)

def tagged(+limits: S.Limits, +instance: String, prepare: Bool, invalidate: Bool, ctx: D.Context,
  registry: Registry, +r: P.Request, a: Admission, h: String) -> Plan:
  match prepare invalidate:
    case True{} _: admitted(limits, instance, admission_matches(a, instance, r), ctx, instance, h, registry, r)
    case False{} True{}: invalidating(limits, instance, String.eq(Resolve.proof(r), ""), ctx, instance, registry, Gate.code(r))
    case False{} False{}: ControlDenied{S.Input{}}

def authenticated(+limits: S.Limits, +instance: String, authentication: Maybe<&2, D.Context>, +tag: U32,
  registry: Registry, +r: P.Request, a: Admission, h: String) -> Plan:
  match authentication:
    case None{}: ControlDenied{S.Authentication{}}
    case Some{ctx}:
      tagged(limits, instance, U32.is_eq(tag, 3), U32.is_eq(tag, 5), ctx, registry, r, a, h)

def routed(+limits: S.Limits, +instance: String, routed: Dispatch.Routed, registry: Registry,
  a: Admission, h: String) -> Plan:
  match routed:
    case Dispatch.Routed{tag, Input.InputReady{+s, +r}}:
      authenticated(limits, instance, D.authenticate(s, Gate.credential(r)), tag, registry, r, a, h)
    case Dispatch.Routed{tag, Input.ErrorMessage{status}}: ControlDenied{status}
    case Dispatch.Routed{tag, Input.ErrorTransport{}}: ControlDenied{S.Failure{}}

# Full ORIGINAL body, including both extension bytes, current published root.
def plan(c: S.Configuration, s: D.State, registry: Registry,
  body: List<&2, U32>, a: Admission, h: String) -> Plan:
  match c:
    case S.Configuration{schema, laws, +limits, +instance}:
      routed(limits, instance, Dispatch.received(limits, body, s), registry, a, h)

def finish(plan: Plan, root: D.State, last: List<&2, U32>, registry: Registry) -> Transition:
  match plan:
    case ControlDenied{status}: ControlResult{root, last, registry, ControlTransaction{S.response_error(status)}}
    case ControlReady{ctx, change, receipt, bytes}: ControlResult{root, last, apply(change, registry), ControlMetadata{receipt, bytes}}

def control(c: S.Configuration, +root: D.State, last: List<&2, U32>, +registry: Registry,
  body: List<&2, U32>, a: Admission, h: String) -> Transition:
  finish(plan(c, root, registry, body, a, h), root, last, registry)
