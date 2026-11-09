# Deterministic control traces generated from the complete dispatchers.
# All registry changes follow successful receipt preparation; delivery failure
# closes without undoing the actual change. This is a model of IO returns, not
# a declaration that a freely chosen trace is the actual Rust/OS execution.
import Base
import ../contract/Data.bend as D
import ../contract/Interface.bend as I
import ../contract/Logic.bend as L
import ../contract/PreparedLaws.bend as H
import ../contract/PreparedProtocol.bend as W
import ../contract/PreparedRegistry.bend as G
import ../contract/Protocol.bend as P
import ../contract/Requirements.bend as R
import ../contract/Resources.bend as X
import ../contract/Semantics.bend as S
import ./Foundations.bend as F
import ./Call.bend as Call
import ./Preparation.bend as Preparation
import ./PreparedControlDispatch.bend as C
import ./PreparedInvalidationDispatch.bend as V
import ./PreparedExtension.bend as E

type ControlKind is Data:
  Prepare{operation: W.Operation, gate: C.Gate}
  Invalidate{cleanup_failed: Bool}

def operation(kind: ControlKind) -> W.Operation:
  match kind:
    case Prepare{op, gate}: op
    case Invalidate{failed}: W.Invalidate{}

def result(kind: ControlKind, c: S.Configuration, initial: D.State, instance: String,
  before: List<&2, G.Entry>, raw: P.Request) -> H.ControlResult:
  match kind:
    case Prepare{op, gate}: C.prepare(c, initial, raw, before, gate)
    case Invalidate{failed}: V.invalidate(c, initial, instance, before, raw, failed)

type SendResult is Data:
  Sent{}
  Interrupted{prefix: List<&2, U32>}

def written(send: SendResult, bytes: List<&2, U32>) -> List<&2, U32>:
  match send:
    case Sent{}: bytes
    case Interrupted{prefix}: prefix

def closes(send: SendResult) -> Bool:
  match send:
    case Sent{}: False{}
    case Interrupted{prefix}: True{}

type ControlEvent is Data:
  Received{operation: W.Operation, raw: P.Request}
  Authenticated{context: Maybe<&2, D.Context>}
  AdmissionReturned{gate: C.Gate}
  ReceiptPrepared{receipt: W.Receipt, frame: Maybe<&2, List<&2, U32>>}
  SealReturned{sealed: Bool}
  RegistryChanged{before: List<&2, G.Entry>, after: List<&2, G.Entry>}
  CleanupReturned{failed: Bool}
  OutputPrepared{bytes: List<&2, U32>}
  Written{bytes: List<&2, U32>}
  Closed{}
  Continued{}

def send_events(send: SendResult, +bytes: List<&2, U32>) -> List<&2, ControlEvent>:
  match send:
    case Sent{}: [OutputPrepared{bytes}, Written{bytes}, Continued{}]
    case Interrupted{prefix}: [OutputPrepared{bytes}, Written{prefix}, Closed{}]

def receipt_prepared(+receipt: W.Receipt, rest: List<&2, ControlEvent>) -> List<&2, ControlEvent>:
  Con{ReceiptPrepared{receipt, W.frame_receipt(receipt)}, rest}

def prepared_trace(fits: Bool, +entry: G.Entry, sealed: Bool,
  +before: List<&2, G.Entry>, after: List<&2, G.Entry>, tail: List<&2, ControlEvent>) -> List<&2, ControlEvent>:
  match fits sealed:
    case False{} _: tail
    case True{} False{}:
      receipt_prepared(W.PreparedReceipt{G.handle(entry)}, Con{SealReturned{False{}}, tail})
    case True{} True{}:
      receipt_prepared(W.PreparedReceipt{G.handle(entry)},
        Con{SealReturned{True{}}, Con{RegistryChanged{before, after}, tail}})

def gate_trace(gate: C.Gate, c: S.Configuration, before: List<&2, G.Entry>,
  after: List<&2, G.Entry>, tail: List<&2, ControlEvent>) -> List<&2, ControlEvent>:
  match gate:
    case C.Refuted{}: Con{AdmissionReturned{C.Refuted{}}, tail}
    case C.Broken{}: Con{AdmissionReturned{C.Broken{}}, tail}
    case C.Candidate{+entry, +sealed}:
      Con{AdmissionReturned{C.Candidate{entry, sealed}},
        prepared_trace(R.fits(R.limit_response(S.limits(c)),
          W.receipt_value(W.PreparedReceipt{G.handle(entry)})), entry, sealed, before, after, tail)}

def invalidation_fitting(fits: Bool, failed: Bool, before: List<&2, G.Entry>,
  after: List<&2, G.Entry>, tail: List<&2, ControlEvent>) -> List<&2, ControlEvent>:
  match fits:
    case False{}: tail
    case True{}:
      receipt_prepared(W.InvalidatedReceipt{},
        Con{RegistryChanged{before, after}, Con{CleanupReturned{failed}, tail}})

def invalidation_lookup(found: Maybe<&2, G.Entry>, c: S.Configuration,
  failed: Bool, before: List<&2, G.Entry>, after: List<&2, G.Entry>,
  tail: List<&2, ControlEvent>) -> List<&2, ControlEvent>:
  match found:
    case None{}: tail
    case Some{entry}:
      invalidation_fitting(R.fits(R.limit_response(S.limits(c)),
        W.receipt_value(W.InvalidatedReceipt{})), failed, before, after, tail)

def invalidation_proof(empty: Bool, c: S.Configuration, failed: Bool,
  instance: String, +before: List<&2, G.Entry>, after: List<&2, G.Entry>,
  raw: P.Request, tail: List<&2, ControlEvent>) -> List<&2, ControlEvent>:
  match empty:
    case False{}: tail
    case True{}:
      invalidation_lookup(G.lookup(instance, I.code(raw), before), c,
        failed, before, after, tail)

def authenticated_trace(authentication: Maybe<&2, D.Context>, kind: ControlKind,
  c: S.Configuration, instance: String, before: List<&2, G.Entry>,
  after: List<&2, G.Entry>, +raw: P.Request, tail: List<&2, ControlEvent>) -> List<&2, ControlEvent>:
  match authentication kind:
    case None{} _: Con{Authenticated{None{}}, tail}
    case Some{+context} Prepare{op, gate}:
      Con{Authenticated{Some{context}}, gate_trace(gate, c, before, after, tail)}
    case Some{+context} Invalidate{failed}:
      Con{Authenticated{Some{context}}, invalidation_proof(String.eq(I.proof(raw), ""),
        c, failed, instance, before, after, raw, tail)}

def trace(~c: S.Configuration, +kind: ControlKind, +initial: D.State, +instance: String,
  +before: List<&2, G.Entry>, +raw: P.Request, bytes: List<&2, U32>,
  send: SendResult) -> List<&2, ControlEvent>:
  Con{Received{operation(kind), raw},
    authenticated_trace(D.authenticate(initial, I.credential(raw)), kind, c, instance,
      before, H.registry(result(kind, c, initial, instance, before, raw)), raw,
      send_events(send, bytes))}

# A prepared receipt grants exactly one registry change. A closed trace cannot
# have a successor event. These checks inspect every generated event.
def ordered(events: List<&2, ControlEvent>, prepared: Bool) -> Bool:
  match events:
    case Nil{}: True{}
    case Con{Received{op, raw}, rest}: ordered(rest, False{})
    case Con{SealReturned{False{}}, rest}: ordered(rest, False{})
    case Con{OutputPrepared{bytes}, rest}: ordered(rest, False{})
    case Con{ReceiptPrepared{receipt, frame}, rest}: ordered(rest, F.some(List<&2, U32>, frame))
    case Con{RegistryChanged{before, after}, rest}: prepared && ordered(rest, False{})
    case Con{Closed{}, rest}:
      match rest:
        case Nil{}: True{}
        case Con{event, later}: False{}
    case Con{event, rest}: ordered(rest, prepared)

# The low-level send contract, not a final delivery postcondition: it records
# the actual primitive return and, for interruption, its returned prefix and
# the same physical call's real transport failure.
def SendPrimitive(send: SendResult, -bytes: List<&2, U32>, -a: I.Environment,
  -native: String, -scenario: I.Scenario, -time: Nat) -> Type:
  match send:
    case Sent{}: Unit
    case Interrupted{prefix}:
      L.E<L.Prefix(U32, prefix, bytes), I.FailureDeliveryReal(a, native, scenario, time)>

law send_return_establishes_exact_delivery_or_actual_prefix:
  for send: SendResult
  for +bytes: List<&2, U32>
  for -a: I.Environment
  for -native: String
  for -scenario: I.Scenario
  for -time: Nat
  for primitive: SendPrimitive(send, bytes, a, native, scenario, time)
  L.Disjunction<{written(send, bytes) == bytes : List<&2, U32>},
    L.E<L.Prefix(U32, written(send, bytes), bytes),
      L.E<I.FailureDeliveryReal(a, native, scenario, time), {closes(send) == True{} : Bool}>>>
def send_return_establishes_exact_delivery_or_actual_prefix(send, bytes, a, native, scenario, time, primitive):
  match send:
    case Sent{}: L.Left{{==}}
    case Interrupted{prefix}:
      L.Both{actual_prefix, real_failure} = primitive
      L.Right{L.Both{actual_prefix, L.Both{real_failure, {==}}}}

law send_trace_is_ordered:
  for send: SendResult
  for bytes: List<&2, U32>
  for prepared: Bool
  {ordered(send_events(send, bytes), prepared) == True{} : Bool}
def send_trace_is_ordered(send, bytes, prepared):
  match send:
    case Sent{}: {==}
    case Interrupted{prefix}: {==}

def frame_exists_some(+value: D.Value,
  witness: &bytes: List<&2, U32> -> P.Message(value, bytes)) ->
  {F.some(List<&2, U32>, P.frame(value)) == True{} : Bool}:
  (bytes, exact) = witness
  Equal.cong(Maybe<&2, List<&2, U32>>, Bool, framed => F.some(List<&2, U32>, framed),
    P.frame(value), Some{bytes}, exact)

def fitting_receipt_has_frame(~c: S.Configuration, +receipt: W.Receipt,
  valid: {R.configuration_is_valid(c) == True{} : Bool},
  fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(receipt)) == True{} : Bool}) ->
  {F.some(List<&2, U32>, W.frame_receipt(receipt)) == True{} : Bool}:
  frame_exists_some(W.receipt_value(receipt),
    Call.response_preparable_has_framing(W.receipt_value(receipt), S.limits(c),
      Preparation.limits_of_configuration(c, valid), fits))

def receipt_before_rest(~c: S.Configuration, +receipt: W.Receipt, +rest: List<&2, ControlEvent>,
  valid: {R.configuration_is_valid(c) == True{} : Bool},
  fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(receipt)) == True{} : Bool},
  later: {ordered(rest, True{}) == True{} : Bool}) ->
  {ordered(receipt_prepared(receipt, rest), False{}) == True{} : Bool}:
  %Equal.sym(Bool, F.some(List<&2, U32>, W.frame_receipt(receipt)), True{},
    fitting_receipt_has_frame(c, receipt, valid, fits)) : {ordered(rest, _) == True{} : Bool}
  later

def prepared_trace_ordered(~c: S.Configuration, fits: Bool, +entry: G.Entry, sealed: Bool,
  +before: List<&2, G.Entry>, +after: List<&2, G.Entry>, +tail: List<&2, ControlEvent>,
  valid: {R.configuration_is_valid(c) == True{} : Bool},
  checked: {R.fits(R.limit_response(S.limits(c)),
    W.receipt_value(W.PreparedReceipt{G.handle(entry)})) == fits : Bool},
  tail_ordered: @prepared: Bool -> {ordered(tail, prepared) == True{} : Bool}) ->
  {ordered(prepared_trace(fits, entry, sealed, before, after, tail), False{}) == True{} : Bool}:
  match fits sealed:
    case False{} _: tail_ordered(False{})
    case True{} False{}:
      receipt_before_rest(c, W.PreparedReceipt{G.handle(entry)},
        Con{SealReturned{False{}}, tail}, valid, checked, tail_ordered(False{}))
    case True{} True{}:
      receipt_before_rest(c, W.PreparedReceipt{G.handle(entry)},
        Con{SealReturned{True{}}, Con{RegistryChanged{before, after}, tail}},
        valid, checked, tail_ordered(False{}))

def gate_trace_ordered(~c: S.Configuration, gate: C.Gate,
  before: List<&2, G.Entry>, after: List<&2, G.Entry>, tail: List<&2, ControlEvent>,
  valid: {R.configuration_is_valid(c) == True{} : Bool},
  tail_ordered: @prepared: Bool -> {ordered(tail, prepared) == True{} : Bool}) ->
  {ordered(gate_trace(gate, c, before, after, tail), False{}) == True{} : Bool}:
  match gate:
    case C.Refuted{}: tail_ordered(False{})
    case C.Broken{}: tail_ordered(False{})
    case C.Candidate{+entry, +sealed}:
      prepared_trace_ordered(c, R.fits(R.limit_response(S.limits(c)),
        W.receipt_value(W.PreparedReceipt{G.handle(entry)})), entry, sealed,
        before, after, tail, valid, {==}, tail_ordered)

def invalidation_fitting_ordered(~c: S.Configuration, fits: Bool, failed: Bool,
  +before: List<&2, G.Entry>, +after: List<&2, G.Entry>, +tail: List<&2, ControlEvent>,
  valid: {R.configuration_is_valid(c) == True{} : Bool},
  checked: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.InvalidatedReceipt{})) == fits : Bool},
  tail_ordered: @prepared: Bool -> {ordered(tail, prepared) == True{} : Bool}) ->
  {ordered(invalidation_fitting(fits, failed, before, after, tail), False{}) == True{} : Bool}:
  match fits:
    case False{}: tail_ordered(False{})
    case True{}:
      receipt_before_rest(c, W.InvalidatedReceipt{},
        Con{RegistryChanged{before, after}, Con{CleanupReturned{failed}, tail}},
        valid, checked, tail_ordered(False{}))

def invalidation_lookup_ordered(~c: S.Configuration, found: Maybe<&2, G.Entry>,
  failed: Bool, before: List<&2, G.Entry>, after: List<&2, G.Entry>, tail: List<&2, ControlEvent>,
  valid: {R.configuration_is_valid(c) == True{} : Bool},
  tail_ordered: @prepared: Bool -> {ordered(tail, prepared) == True{} : Bool}) ->
  {ordered(invalidation_lookup(found, c, failed, before, after, tail), False{}) == True{} : Bool}:
  match found:
    case None{}: tail_ordered(False{})
    case Some{entry}:
      invalidation_fitting_ordered(c, R.fits(R.limit_response(S.limits(c)),
        W.receipt_value(W.InvalidatedReceipt{})), failed, before, after, tail,
        valid, {==}, tail_ordered)

def invalidation_proof_ordered(~c: S.Configuration, empty: Bool, failed: Bool,
  instance: String, +before: List<&2, G.Entry>, after: List<&2, G.Entry>, raw: P.Request,
  tail: List<&2, ControlEvent>, valid: {R.configuration_is_valid(c) == True{} : Bool},
  tail_ordered: @prepared: Bool -> {ordered(tail, prepared) == True{} : Bool}) ->
  {ordered(invalidation_proof(empty, c, failed, instance, before, after, raw, tail), False{}) == True{} : Bool}:
  match empty:
    case False{}: tail_ordered(False{})
    case True{}:
      invalidation_lookup_ordered(c, G.lookup(instance, I.code(raw), before), failed,
        before, after, tail, valid, tail_ordered)

def authenticated_trace_ordered(~c: S.Configuration, authentication: Maybe<&2, D.Context>,
  kind: ControlKind, instance: String, before: List<&2, G.Entry>, after: List<&2, G.Entry>,
  +raw: P.Request, tail: List<&2, ControlEvent>, valid: {R.configuration_is_valid(c) == True{} : Bool},
  tail_ordered: @prepared: Bool -> {ordered(tail, prepared) == True{} : Bool}) ->
  {ordered(authenticated_trace(authentication, kind, c, instance, before,
    after, raw, tail), False{}) == True{} : Bool}:
  match authentication kind:
    case None{} _: tail_ordered(False{})
    case Some{context} Prepare{op, gate}:
      gate_trace_ordered(c, gate, before, after, tail, valid, tail_ordered)
    case Some{context} Invalidate{failed}:
      invalidation_proof_ordered(c, String.eq(I.proof(raw), ""), failed, instance,
        before, after, raw, tail, valid, tail_ordered)

law every_control_mutation_follows_one_successfully_framed_receipt:
  for ~c: S.Configuration
  for +kind: ControlKind
  for +initial: D.State
  for +instance: String
  for +before: List<&2, G.Entry>
  for +raw: P.Request
  for +bytes: List<&2, U32>
  for +send: SendResult
  for valid: {R.configuration_is_valid(c) == True{} : Bool}
  {ordered(trace(c, kind, initial, instance, before, raw, bytes, send), False{}) == True{} : Bool}
def every_control_mutation_follows_one_successfully_framed_receipt(c, kind, initial,
  instance, before, raw, bytes, send, valid):
  authenticated_trace_ordered(c, D.authenticate(initial, I.credential(raw)), kind,
    instance, before, H.registry(result(kind, c, initial, instance, before, raw)),
    raw, send_events(send, bytes), valid, prepared => send_trace_is_ordered(send, bytes, prepared))

# Replaying every generated mutation, including failed cleanup and lost
# delivery, must yield the dispatcher's complete final registry. A list with
# conveniently omitted changes would fail this equality.
def replay(events: List<&2, ControlEvent>, registry: List<&2, G.Entry>) -> List<&2, G.Entry>:
  match events:
    case Nil{}: registry
    case Con{RegistryChanged{before, after}, rest}: replay(rest, after)
    case Con{event, rest}: replay(rest, registry)

law send_cannot_undo_registry_mutation:
  for send: SendResult
  for bytes: List<&2, U32>
  for +registry: List<&2, G.Entry>
  {replay(send_events(send, bytes), registry) == registry : List<&2, G.Entry>}
def send_cannot_undo_registry_mutation(send, bytes, registry):
  match send:
    case Sent{}: {==}
    case Interrupted{prefix}: {==}

def replay_prepared(fits: Bool, +entry: G.Entry, sealed: Bool,
  +initial: D.State, +before: List<&2, G.Entry>, +tail: List<&2, ControlEvent>,
  neutral: @registry: List<&2, G.Entry> -> {replay(tail, registry) == registry : List<&2, G.Entry>}) ->
  {replay(prepared_trace(fits, entry, sealed, before,
    H.registry(C.fitting_result(fits, sealed, initial, entry, before)), tail), before) ==
    H.registry(C.fitting_result(fits, sealed, initial, entry, before)) : List<&2, G.Entry>}:
  match fits sealed:
    case False{} _: neutral(before)
    case True{} False{}: neutral(before)
    case True{} True{}: neutral(Con{entry, before})

def replay_gate(~c: S.Configuration, +gate: C.Gate,
  +initial: D.State, +before: List<&2, G.Entry>, +tail: List<&2, ControlEvent>,
  neutral: @registry: List<&2, G.Entry> -> {replay(tail, registry) == registry : List<&2, G.Entry>}) ->
  {replay(gate_trace(gate, c, before, H.registry(C.gate_result(gate, c, initial, before)), tail), before) ==
    H.registry(C.gate_result(gate, c, initial, before)) : List<&2, G.Entry>}:
  match gate:
    case C.Refuted{}: neutral(before)
    case C.Broken{}: neutral(before)
    case C.Candidate{+entry, +sealed}:
      replay_prepared(R.fits(R.limit_response(S.limits(c)),
        W.receipt_value(W.PreparedReceipt{G.handle(entry)})), entry, sealed,
        initial, before, tail, neutral)

def replay_preparation_auth(~c: S.Configuration, +authentication: Maybe<&2, D.Context>,
  op: W.Operation, +gate: C.Gate, +initial: D.State, instance: String,
  +before: List<&2, G.Entry>, raw: P.Request, +tail: List<&2, ControlEvent>,
  neutral: @registry: List<&2, G.Entry> -> {replay(tail, registry) == registry : List<&2, G.Entry>}) ->
  {replay(authenticated_trace(authentication, Prepare{op, gate}, c, instance, before,
    H.registry(C.authenticated_result(authentication, gate, c, initial, before)), raw, tail), before) ==
    H.registry(C.authenticated_result(authentication, gate, c, initial, before)) : List<&2, G.Entry>}:
  match authentication:
    case None{}: neutral(before)
    case Some{context}: replay_gate(c, gate, initial, before, tail, neutral)

def cleanup_registry_before(+failed: Bool, +initial: D.State,
  +before: List<&2, G.Entry>, status: S.Status) ->
  {before == H.registry(H.cleanup_invalidation(failed,
    H.ControlResult{initial, before, H.Error{status}})) : List<&2, G.Entry>}:
  Equal.sym(List<&2, G.Entry>, H.registry(H.cleanup_invalidation(failed,
    H.ControlResult{initial, before, H.Error{status}})), before,
    E.cleanup_cannot_restore_registry(failed, H.ControlResult{initial, before, H.Error{status}}))

def replay_invalidation_fitting(fits: Bool, +failed: Bool, +initial: D.State,
  +instance: String, +before: List<&2, G.Entry>, +raw: P.Request,
  +tail: List<&2, ControlEvent>,
  neutral: @registry: List<&2, G.Entry> -> {replay(tail, registry) == registry : List<&2, G.Entry>}) ->
  {replay(invalidation_fitting(fits, failed, before,
    H.registry(H.cleanup_invalidation(failed,
      H.invalidate_fits(fits, initial, instance, I.code(raw), before))), tail), before) ==
    H.registry(H.cleanup_invalidation(failed,
      H.invalidate_fits(fits, initial, instance, I.code(raw), before))) : List<&2, G.Entry>}:
  match fits:
    case False{}:
      Equal.trans(List<&2, G.Entry>, replay(tail, before), before,
        H.registry(H.cleanup_invalidation(failed, H.ControlResult{initial, before, H.Error{S.Limit{}}})),
        neutral(before), cleanup_registry_before(failed, initial, before, S.Limit{}))
    case True{}:
      neutral(H.registry(H.cleanup_invalidation(failed,
        H.invalidate_fits(True{}, initial, instance, I.code(raw), before))))

def replay_invalidation_lookup(~c: S.Configuration, +found: Maybe<&2, G.Entry>,
  +failed: Bool, +initial: D.State, +instance: String, +before: List<&2, G.Entry>,
  +raw: P.Request, +tail: List<&2, ControlEvent>,
  neutral: @registry: List<&2, G.Entry> -> {replay(tail, registry) == registry : List<&2, G.Entry>}) ->
  {replay(invalidation_lookup(found, c, failed, before,
    H.registry(H.cleanup_invalidation(failed,
      H.invalidate_found(found, c, initial, instance, I.code(raw), before))), tail), before) ==
    H.registry(H.cleanup_invalidation(failed,
      H.invalidate_found(found, c, initial, instance, I.code(raw), before))) : List<&2, G.Entry>}:
  match found:
    case None{}:
      Equal.trans(List<&2, G.Entry>, replay(tail, before), before,
        H.registry(H.cleanup_invalidation(failed, H.ControlResult{initial, before, H.Error{S.Failure{}}})),
        neutral(before), cleanup_registry_before(failed, initial, before, S.Failure{}))
    case Some{entry}:
      replay_invalidation_fitting(R.fits(R.limit_response(S.limits(c)),
        W.receipt_value(W.InvalidatedReceipt{})), failed, initial, instance, before, raw, tail, neutral)

def replay_invalidation_proof(~c: S.Configuration, +empty: Bool, +failed: Bool,
  +initial: D.State, +instance: String, +before: List<&2, G.Entry>, +raw: P.Request,
  +tail: List<&2, ControlEvent>,
  neutral: @registry: List<&2, G.Entry> -> {replay(tail, registry) == registry : List<&2, G.Entry>}) ->
  {replay(invalidation_proof(empty, c, failed, instance, before,
    H.registry(V.after_proof(empty, c, initial, instance, before, raw, failed)), raw, tail), before) ==
    H.registry(V.after_proof(empty, c, initial, instance, before, raw, failed)) : List<&2, G.Entry>}:
  match empty:
    case False{}: neutral(before)
    case True{}:
      replay_invalidation_lookup(c, G.lookup(instance, I.code(raw), before), failed,
        initial, instance, before, raw, tail, neutral)

def replay_invalidation_auth(~c: S.Configuration, +authentication: Maybe<&2, D.Context>,
  +failed: Bool, +initial: D.State, +instance: String, +before: List<&2, G.Entry>,
  +raw: P.Request, +tail: List<&2, ControlEvent>,
  neutral: @registry: List<&2, G.Entry> -> {replay(tail, registry) == registry : List<&2, G.Entry>}) ->
  {replay(authenticated_trace(authentication, Invalidate{failed}, c, instance, before,
    H.registry(V.after_authentication(authentication, c, initial, instance, before, raw, failed)), raw, tail), before) ==
    H.registry(V.after_authentication(authentication, c, initial, instance, before, raw, failed)) : List<&2, G.Entry>}:
  match authentication:
    case None{}: neutral(before)
    case Some{context}:
      replay_invalidation_proof(c, String.eq(I.proof(raw), ""), failed,
        initial, instance, before, raw, tail, neutral)

law trace_replay_is_exact_complete_controller_registry:
  for ~c: S.Configuration
  for +kind: ControlKind
  for +initial: D.State
  for +instance: String
  for +before: List<&2, G.Entry>
  for +raw: P.Request
  for +bytes: List<&2, U32>
  for +send: SendResult
  {replay(trace(c, kind, initial, instance, before, raw, bytes, send), before) ==
    H.registry(result(kind, c, initial, instance, before, raw)) : List<&2, G.Entry>}
def trace_replay_is_exact_complete_controller_registry(c, kind, initial, instance, before, raw, bytes, send):
  match kind:
    case Prepare{op, gate}:
      replay_preparation_auth(c, D.authenticate(initial, I.credential(raw)),
        op, gate, initial, instance, before, raw, send_events(send, bytes),
        registry => send_cannot_undo_registry_mutation(send, bytes, registry))
    case Invalidate{failed}:
      replay_invalidation_auth(c, D.authenticate(initial, I.credential(raw)),
        failed, initial, instance, before, raw, send_events(send, bytes),
        registry => send_cannot_undo_registry_mutation(send, bytes, registry))

# A single control-service theorem covers both computed controllers. Its
# evidence contains only external tool/artifact contracts for selected calls;
# it supplies no final state, outcome, publication or delivery conclusion.
def ControlEvidence(~c: S.Configuration, kind: ControlKind, +initial: D.State,
  +instance: String, +before: List<&2, G.Entry>, +raw: P.Request,
  -a: I.Environment, -artifacts: H.Artifacts, -native: String,
  -world: Nat, -time: Nat, -input: X.Reception) -> Type:
  match kind:
    case Prepare{op, gate}:
      L.E<H.PreparationOperation(op),
        C.ToolsAfterAuthentication(D.authenticate(initial, I.credential(raw)),
          gate, op, a, artifacts, native, world, time, c, initial, input, instance, before, raw)>
    case Invalidate{failed}:
      V.CleanupEvidence(D.authenticate(initial, I.credential(raw)), a, artifacts,
        native, world, time, c, initial, input, instance, before, raw, failed)

law complete_decoded_control_service_outcome:
  for ~c: S.Configuration
  for +kind: ControlKind
  for +initial: D.State
  for +instance: String
  for +before: List<&2, G.Entry>
  for +raw: P.Request
  for -a: I.Environment
  for -artifacts: H.Artifacts
  for -native: String
  for -world: Nat
  for -time: Nat
  for -input: X.Reception
  for -previous: List<&2, U32>
  for valid: {R.configuration_is_valid(c) == True{} : Bool}
  for received: W.Received(c, input, W.Extension{operation(kind), raw})
  for facts: ControlEvidence(c, kind, initial, instance, before, raw,
    a, artifacts, native, world, time, input)
  exs bytes: List<&2, U32>
  H.ControlOutcome(a, artifacts, native, world, c, initial, input, time,
    instance, before, operation(kind), raw, result(kind, c, initial, instance, before, raw),
    previous, previous, bytes)
def complete_decoded_control_service_outcome(c, kind, initial, instance, before,
  raw, a, artifacts, native, world, time, input, previous, valid, received, facts):
  match kind:
    case Prepare{op, gate}:
      L.Both{preparation, evidence} = facts
      C.complete_preparation_control_outcome(c, op, a, artifacts, native, world,
        time, initial, input, instance, before, raw, gate, previous,
        preparation, valid, received, evidence)
    case Invalidate{failed}:
      V.complete_invalidation_control_outcome(c, a, artifacts, native, world,
        time, initial, input, instance, before, raw, failed, previous,
        valid, received, facts)
