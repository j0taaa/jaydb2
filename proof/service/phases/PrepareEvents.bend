# Exact successful preparation phases, derived from the actual dispatcher and
# actual register function. Authentication/freshness/checker/IO facts will be
# supplied by their separate local primitive and authority proofs.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Interface.bend as I
import ../../../contract/Logic.bend as L
import ../../../contract/PreparedLaws.bend as H
import ../../../contract/PreparedProtocol.bend as W
import ../../../contract/PreparedRegistry.bend as G
import ../../../contract/Protocol.bend as P
import ../../../contract/Requirements.bend as R
import ../../../contract/Semantics.bend as S
import ../../PreparedExtension.bend as Extension
import ../specification/ServiceLaws.bend as E
import ../model/FrameBounds.bend as B
import ./PreparePhases.bend as V

def registered(+before: E.Snapshot, +entry: G.Entry) -> H.ControlResult:
  H.ControlResult{E.database(before), Con{entry, E.registry(before)}, H.Metadata{W.PreparedReceipt{G.handle(entry)}}}

def sealed_success(+before: E.Snapshot, +entry: G.Entry, +bytes: List<&2, U32>, send: V.SendReturn) -> V.PreparationRun:
  V.push(V.ArtifactSealed{entry}, V.register_result(registered(before, entry), before, entry, bytes, send))

def framed_success(+before: E.Snapshot, +entry: G.Entry, +bytes: List<&2, U32>, send: V.SendReturn) -> V.PreparationRun:
  V.push(V.ReceiptPrepared{W.PreparedReceipt{G.handle(entry)}, bytes}, sealed_success(before, entry, bytes, send))

def allocated_success(+before: E.Snapshot, +entry: G.Entry, bytes: List<&2, U32>, send: V.SendReturn) -> V.PreparationRun:
  V.push(V.HandleChosen{G.handle(entry)}, framed_success(before, entry, bytes, send))

def checked_success(mode: V.Mode, raw: P.Request, context: D.Context,
  before: E.Snapshot, entry: G.Entry, bytes: List<&2, U32>, send: V.SendReturn) -> V.PreparationRun:
  V.push(V.Accepted{W.Extension{V.operation(mode), raw}, context}, allocated_success(before, entry, bytes, send))

def success(+mode: V.Mode, +raw: P.Request, +context: D.Context,
  before: E.Snapshot, entry: G.Entry, bytes: List<&2, U32>, send: V.SendReturn) -> V.PreparationRun:
  V.push(V.WireReceived{W.Extension{V.operation(mode), raw}},
    V.push(V.IdentityEstablished{W.Extension{V.operation(mode), raw}, Some{context}},
      checked_success(mode, raw, context, before, entry, bytes, send)))

def sealed_exact(~c: S.Configuration, +mode: V.Mode, +raw: P.Request, +before: E.Snapshot,
  +handle: String, +seal: String, +bytes: List<&2, U32>, +send: V.SendReturn,
  fresh: {G.lookup(E.instance(before), handle, E.registry(before)) == None{} : Maybe<&2, G.Entry>},
  fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{handle})) == True{} : Bool}) ->
  {V.seal_result(c, V.SealSucceeded{seal}, mode, raw, before, handle, bytes, send) ==
    sealed_success(before, V.entry(mode, raw, E.instance(before), handle, seal), bytes, send) : V.PreparationRun}:
  +entry: G.Entry = V.entry(mode, raw, E.instance(before), handle, seal)
  Equal.cong(H.ControlResult, V.PreparationRun,
    result => V.push(V.ArtifactSealed{entry}, V.register_result(result, before, entry, bytes, send)),
    H.register(c, E.database(before), E.instance(before), entry, E.registry(before)), registered(before, entry),
    Extension.fresh_fitting_registration_returns_receipt_and_exact_entry(c, E.database(before), E.instance(before), entry, E.registry(before), fresh, fits))

def framed_exact(~c: S.Configuration, +mode: V.Mode, +raw: P.Request, +before: E.Snapshot,
  +handle: String, +seal: String, +bytes: List<&2, U32>, +send: V.SendReturn,
  fresh: {G.lookup(E.instance(before), handle, E.registry(before)) == None{} : Maybe<&2, G.Entry>},
  fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{handle})) == True{} : Bool},
  frame: {W.frame_receipt(W.PreparedReceipt{handle}) == Some{bytes} : Maybe<&2, List<&2, U32>>}) ->
  {V.fitting_frame(c, W.frame_receipt(W.PreparedReceipt{handle}), mode, raw, before, handle, V.SealSucceeded{seal}, send) ==
    framed_success(before, V.entry(mode, raw, E.instance(before), handle, seal), bytes, send) : V.PreparationRun}:
  %Equal.sym(Maybe<&2, List<&2, U32>>, W.frame_receipt(W.PreparedReceipt{handle}), Some{bytes}, frame) :
    {V.fitting_frame(c, _, mode, raw, before, handle, V.SealSucceeded{seal}, send) ==
      framed_success(before, V.entry(mode, raw, E.instance(before), handle, seal), bytes, send) : V.PreparationRun}
  Equal.cong(V.PreparationRun, V.PreparationRun, run => V.push(V.ReceiptPrepared{W.PreparedReceipt{handle}, bytes}, run),
    V.seal_result(c, V.SealSucceeded{seal}, mode, raw, before, handle, bytes, send),
    sealed_success(before, V.entry(mode, raw, E.instance(before), handle, seal), bytes, send),
    sealed_exact(c, mode, raw, before, handle, seal, bytes, send, fresh, fits))

def allocated_exact(~c: S.Configuration, +mode: V.Mode, +raw: P.Request, +before: E.Snapshot,
  +handle: String, +seal: String, +bytes: List<&2, U32>, +send: V.SendReturn,
  fresh: {G.lookup(E.instance(before), handle, E.registry(before)) == None{} : Maybe<&2, G.Entry>},
  +fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{handle})) == True{} : Bool},
  frame: {W.frame_receipt(W.PreparedReceipt{handle}) == Some{bytes} : Maybe<&2, List<&2, U32>>}) ->
  {V.allocated(c, V.AllocatorChosen{handle}, mode, raw, before, V.SealSucceeded{seal}, send) ==
    allocated_success(before, V.entry(mode, raw, E.instance(before), handle, seal), bytes, send) : V.PreparationRun}:
  %Equal.sym(Bool, R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{handle})), True{}, fits) :
    {V.push(V.HandleChosen{handle}, V.receipt_fit(c, _, mode, raw, before, handle, V.SealSucceeded{seal}, send)) ==
      allocated_success(before, V.entry(mode, raw, E.instance(before), handle, seal), bytes, send) : V.PreparationRun}
  Equal.cong(V.PreparationRun, V.PreparationRun, run => V.push(V.HandleChosen{handle}, run),
    V.fitting_frame(c, W.frame_receipt(W.PreparedReceipt{handle}), mode, raw, before, handle, V.SealSucceeded{seal}, send),
    framed_success(before, V.entry(mode, raw, E.instance(before), handle, seal), bytes, send),
    framed_exact(c, mode, raw, before, handle, seal, bytes, send, fresh, fits, frame))

law successful_preparation_has_the_exact_dispatcher_phases:
  for ~c: S.Configuration
  for +mode: V.Mode
  for +raw: P.Request
  for +before: E.Snapshot
  for +context: D.Context
  for +handle: String
  for +seal: String
  for +bytes: List<&2, U32>
  for +send: V.SendReturn
  for authenticated: {D.authenticate(E.database(before), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>}
  for fresh: {G.lookup(E.instance(before), handle, E.registry(before)) == None{} : Maybe<&2, G.Entry>}
  for fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{handle})) == True{} : Bool}
  for frame: {W.frame_receipt(W.PreparedReceipt{handle}) == Some{bytes} : Maybe<&2, List<&2, U32>>}
  {V.run(c, mode, raw, before, V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send}) ==
    success(mode, raw, context, before, V.entry(mode, raw, E.instance(before), handle, seal), bytes, send) : V.PreparationRun}
def successful_preparation_has_the_exact_dispatcher_phases(c, mode, raw, before, context, handle, seal, bytes, send, authenticated, fresh, fits, frame):
  %Equal.sym(Maybe<&2, D.Context>, D.authenticate(E.database(before), I.credential(raw)), Some{context}, authenticated) :
    {V.push(V.WireReceived{W.Extension{V.operation(mode), raw}},
      V.push(V.IdentityEstablished{W.Extension{V.operation(mode), raw}, _},
        V.authenticated(c, _, mode, raw, before, V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send}))) ==
      success(mode, raw, context, before, V.entry(mode, raw, E.instance(before), handle, seal), bytes, send) : V.PreparationRun}
  Equal.cong(V.PreparationRun, V.PreparationRun,
    run => V.push(V.WireReceived{W.Extension{V.operation(mode), raw}},
      V.push(V.IdentityEstablished{W.Extension{V.operation(mode), raw}, Some{context}},
        V.push(V.Accepted{W.Extension{V.operation(mode), raw}, context}, run))),
    V.allocated(c, V.AllocatorChosen{handle}, mode, raw, before, V.SealSucceeded{seal}, send),
    allocated_success(before, V.entry(mode, raw, E.instance(before), handle, seal), bytes, send),
    allocated_exact(c, mode, raw, before, handle, seal, bytes, send, fresh, fits, frame))

law successful_phase_list_contains_the_exact_registry_event_at_six:
  for mode: V.Mode
  for raw: P.Request
  for context: D.Context
  for +before: E.Snapshot
  for +entry: G.Entry
  for bytes: List<&2, U32>
  for send: V.SendReturn
  {B.query(V.PreparationEvent, V.events(success(mode, raw, context, before, entry, bytes, send)), 6n) ==
    Some{V.RegistryChanged{entry, before, V.registered_snapshot(before, registered(before, entry))}} : Maybe<&2, V.PreparationEvent>}
def successful_phase_list_contains_the_exact_registry_event_at_six(mode, raw, context, before, entry, bytes, send):
  match send:
    case V.SendPending{}: {==}
    case V.SendComplete{}: {==}
    case V.SendInterrupted{prefix}: {==}

law actual_successful_dispatcher_supplies_the_registry_query:
  for ~c: S.Configuration
  for +mode: V.Mode
  for +raw: P.Request
  for +before: E.Snapshot
  for +context: D.Context
  for +handle: String
  for +seal: String
  for +bytes: List<&2, U32>
  for +send: V.SendReturn
  for authenticated: {D.authenticate(E.database(before), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>}
  for fresh: {G.lookup(E.instance(before), handle, E.registry(before)) == None{} : Maybe<&2, G.Entry>}
  for fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{handle})) == True{} : Bool}
  for frame: {W.frame_receipt(W.PreparedReceipt{handle}) == Some{bytes} : Maybe<&2, List<&2, U32>>}
  {B.query(V.PreparationEvent, V.events(V.run(c, mode, raw, before, V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send})), 6n) ==
    Some{V.RegistryChanged{V.entry(mode, raw, E.instance(before), handle, seal), before,
      V.registered_snapshot(before, registered(before, V.entry(mode, raw, E.instance(before), handle, seal)))}} : Maybe<&2, V.PreparationEvent>}
def actual_successful_dispatcher_supplies_the_registry_query(c, mode, raw, before, context, handle, seal, bytes, send, authenticated, fresh, fits, frame):
  Equal.trans(Maybe<&2, V.PreparationEvent>,
    B.query(V.PreparationEvent, V.events(V.run(c, mode, raw, before, V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send})), 6n),
    B.query(V.PreparationEvent, V.events(success(mode, raw, context, before, V.entry(mode, raw, E.instance(before), handle, seal), bytes, send)), 6n),
    Some{V.RegistryChanged{V.entry(mode, raw, E.instance(before), handle, seal), before,
      V.registered_snapshot(before, registered(before, V.entry(mode, raw, E.instance(before), handle, seal)))}},
    Equal.cong(V.PreparationRun, Maybe<&2, V.PreparationEvent>,
      run => B.query(V.PreparationEvent, V.events(run), 6n),
      V.run(c, mode, raw, before, V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send}),
      success(mode, raw, context, before, V.entry(mode, raw, E.instance(before), handle, seal), bytes, send),
      successful_preparation_has_the_exact_dispatcher_phases(c, mode, raw, before, context, handle, seal, bytes, send, authenticated, fresh, fits, frame)),
    successful_phase_list_contains_the_exact_registry_event_at_six(mode, raw, context, before, V.entry(mode, raw, E.instance(before), handle, seal), bytes, send))

law successful_control_preserves_instance_database_and_last_transaction_response:
  for mode: V.Mode
  for raw: P.Request
  for context: D.Context
  for +before: E.Snapshot
  for +entry: G.Entry
  for bytes: List<&2, U32>
  for send: V.SendReturn
  {V.snapshot(success(mode, raw, context, before, entry, bytes, send)) ==
    E.Snapshot{E.instance(before), E.database(before), E.last_response(before), Con{entry, E.registry(before)}} : E.Snapshot}
def successful_control_preserves_instance_database_and_last_transaction_response(mode, raw, context, before, entry, bytes, send):
  match send:
    case V.SendPending{}: {==}
    case V.SendComplete{}: {==}
    case V.SendInterrupted{prefix}: {==}

law successful_control_retains_its_result_after_every_send_return:
  for mode: V.Mode
  for raw: P.Request
  for context: D.Context
  for +before: E.Snapshot
  for +entry: G.Entry
  for bytes: List<&2, U32>
  for send: V.SendReturn
  {V.result(success(mode, raw, context, before, entry, bytes, send)) == Some{registered(before, entry)} : Maybe<&2, H.ControlResult>}
def successful_control_retains_its_result_after_every_send_return(mode, raw, context, before, entry, bytes, send):
  match send:
    case V.SendPending{}: {==}
    case V.SendComplete{}: {==}
    case V.SendInterrupted{prefix}: {==}

def accepted_prefix(+mode: V.Mode, +raw: P.Request, +context: D.Context, tail: V.PreparationRun) ->
  {B.query(V.PreparationEvent, V.events(V.push(V.WireReceived{W.Extension{V.operation(mode), raw}},
    V.push(V.IdentityEstablished{W.Extension{V.operation(mode), raw}, Some{context}},
      V.push(V.Accepted{W.Extension{V.operation(mode), raw}, context}, tail)))), 2n) ==
    Some{V.Accepted{W.Extension{V.operation(mode), raw}, context}} : Maybe<&2, V.PreparationEvent>}:
  match tail:
    case V.PreparationRun{events, result, snapshot, waiting, closed}: {==}

law checker_acceptance_is_retained_for_every_later_primitive_return:
  for ~c: S.Configuration
  for +mode: V.Mode
  for +raw: P.Request
  for +before: E.Snapshot
  for +context: D.Context
  for +allocation: V.AllocatorReturn
  for +seal: V.SealReturn
  for +send: V.SendReturn
  for authenticated: {D.authenticate(E.database(before), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>}
  {B.query(V.PreparationEvent, V.events(V.run(c, mode, raw, before, V.Returns{V.CheckerAccepted{}, allocation, seal, send})), 2n) ==
    Some{V.Accepted{W.Extension{V.operation(mode), raw}, context}} : Maybe<&2, V.PreparationEvent>}
def checker_acceptance_is_retained_for_every_later_primitive_return(c, mode, raw, before, context, allocation, seal, send, authenticated):
  %Equal.sym(Maybe<&2, D.Context>, D.authenticate(E.database(before), I.credential(raw)), Some{context}, authenticated) :
    {B.query(V.PreparationEvent, V.events(V.push(V.WireReceived{W.Extension{V.operation(mode), raw}},
      V.push(V.IdentityEstablished{W.Extension{V.operation(mode), raw}, _},
        V.authenticated(c, _, mode, raw, before, V.Returns{V.CheckerAccepted{}, allocation, seal, send})))), 2n) ==
      Some{V.Accepted{W.Extension{V.operation(mode), raw}, context}} : Maybe<&2, V.PreparationEvent>}
  accepted_prefix(mode, raw, context, V.allocated(c, allocation, mode, raw, before, seal, send))
