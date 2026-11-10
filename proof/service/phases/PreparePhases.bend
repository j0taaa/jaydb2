# Preparation AFTER actual selection/framing/decoding. The caller retains those
# microevents. Checker, post-check setup/allocator, receipt, seal, mutation,
# conclusion and delivery are distinct stages; accepted checking is never
# erased by a later primitive error. This is a pure operational source, not
# an assertion that a chosen observer is the native execution.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Bytes.bend as B
import ../../../contract/Interface.bend as I
import ../../../contract/Logic.bend as L
import ../../../contract/PreparedLaws.bend as H
import ../../../contract/PreparedProtocol.bend as W
import ../../../contract/PreparedRegistry.bend as G
import ../../../contract/Protocol.bend as P
import ../../../contract/Requirements.bend as R
import ../../../contract/Resources.bend as X
import ../../../contract/Semantics.bend as S
import ../../Foundations.bend as F
import ../../SourceService.bend as Source
import ../../HostTransitions.bend as Host
import ../../PreparedControlDispatch.bend as C
import ../../Call.bend as Call
import ../specification/ServiceLaws.bend as E

type Mode is Data:
  PrepareMode{}
  ReadMode{}

def operation(mode: Mode) -> W.Operation:
  match mode:
    case PrepareMode{}: W.Prepare{}
    case ReadMode{}: W.PrepareRead{}

def read_only(mode: Mode) -> Bool:
  match mode:
    case PrepareMode{}: False{}
    case ReadMode{}: True{}

type CheckerReturn is Data:
  CheckerPending{}
  CheckerAccepted{}
  CheckerRefuted{}
  CheckerFailed{stage: X.Stage, identifier: String, fatal: Bool}

# The interval also covers actual compile/setup/report/entropy work after the
# successful checker return and before a handle exists, with the precise real
# failure stage supplied by the primitive evidence.
type AllocatorReturn is Data:
  AllocatorPending{}
  AllocatorChosen{handle: String}
  AllocatorFailed{stage: X.Stage, identifier: String, fatal: Bool}

type SealReturn is Data:
  SealPending{}
  SealSucceeded{seal: String}
  SealFailed{stage: X.Stage, identifier: String, fatal: Bool}

type SendReturn is Data:
  SendPending{}
  SendComplete{}
  SendInterrupted{prefix: List<&2, U32>}

type Returns is Data:
  Returns{checker: CheckerReturn, allocator: AllocatorReturn, seal: SealReturn, send: SendReturn}

type PreparationEvent is Data:
  WireReceived{wire: W.WireRequest}
  IdentityEstablished{wire: W.WireRequest, context: Maybe<&2, D.Context>}
  Accepted{wire: W.WireRequest, context: D.Context}
  Refuted{wire: W.WireRequest, context: D.Context}
  PrimitiveFailed{stage: X.Stage, identifier: String, fatal: Bool}
  HandleChosen{handle: String}
  ReceiptPrepared{receipt: W.Receipt, bytes: List<&2, U32>}
  ArtifactSealed{entry: G.Entry}
  RegistryChanged{entry: G.Entry, before: E.Snapshot, after: E.Snapshot}
  ReceiptConcluded{receipt: W.Receipt, result: H.ControlResult, snapshot: E.Snapshot, closes: Bool}
  ErrorPrepared{status: S.Status, bytes: List<&2, U32>}
  ErrorConcluded{status: S.Status, snapshot: E.Snapshot, closes: Bool}
  Delivered{bytes: List<&2, U32>}
  Interrupted{prefix: List<&2, U32>}
  Closed{}

type PreparationRun is Data:
  PreparationRun{events: List<&2, PreparationEvent>, result: Maybe<&2, H.ControlResult>, snapshot: E.Snapshot, waiting: Bool, closed: Bool}

def events(run: PreparationRun) -> List<&2, PreparationEvent>:
  PreparationRun{events, result, snapshot, waiting, closed} = run
  events

def result(run: PreparationRun) -> Maybe<&2, H.ControlResult>:
  PreparationRun{events, result, snapshot, waiting, closed} = run
  result

def snapshot(run: PreparationRun) -> E.Snapshot:
  PreparationRun{events, result, snapshot, waiting, closed} = run
  snapshot

def push(event: PreparationEvent, run: PreparationRun) -> PreparationRun:
  PreparationRun{events, result, snapshot, waiting, closed} = run
  PreparationRun{Con{event, events}, result, snapshot, waiting, closed}

def pending(snapshot: E.Snapshot) -> PreparationRun:
  PreparationRun{Nil{}, None{}, snapshot, True{}, False{}}

# This branch represents an impossible internal packet under the later proved
# configuration/receipt invariants. It emits no fabricated result or mutation.
def inconsistent(snapshot: E.Snapshot) -> PreparationRun:
  PreparationRun{Nil{}, None{}, snapshot, False{}, False{}}

def delivery(send: SendReturn, +bytes: List<&2, U32>, completed: H.ControlResult, snapshot: E.Snapshot) -> PreparationRun:
  match send:
    case SendPending{}: PreparationRun{Nil{}, Some{completed}, snapshot, True{}, False{}}
    case SendComplete{}: PreparationRun{[Delivered{bytes}], Some{completed}, snapshot, False{}, False{}}
    case SendInterrupted{prefix}: PreparationRun{[Interrupted{prefix}, Closed{}], Some{completed}, snapshot, False{}, True{}}

def error_framed(+status: S.Status, +snapshot: E.Snapshot, send: SendReturn, frame: Maybe<&2, List<&2, U32>>) -> PreparationRun:
  match frame:
    case None{}: inconsistent(snapshot)
    case Some{+bytes}:
      push(ErrorPrepared{status, bytes}, push(ErrorConcluded{status, snapshot, False{}},
        delivery(send, bytes, H.ControlResult{E.database(snapshot), E.registry(snapshot), H.Error{status}}, snapshot)))

def error(+status: S.Status, snapshot: E.Snapshot, send: SendReturn) -> PreparationRun:
  error_framed(status, snapshot, send, P.frame(S.response_value(S.response_error(status))))

def failed(stage: X.Stage, identifier: String, fatal: Bool, snapshot: E.Snapshot, send: SendReturn) -> PreparationRun:
  match fatal:
    case True{}: PreparationRun{[PrimitiveFailed{stage, identifier, True{}}, Closed{}], None{}, snapshot, False{}, True{}}
    case False{}: push(PrimitiveFailed{stage, identifier, False{}}, error(S.Failure{}, snapshot, send))

def entry(mode: Mode, +raw: P.Request, instance: String, handle: String, seal: String) -> G.Entry:
  G.Entry{instance, handle, I.code(raw), I.proof(raw), read_only(mode), seal}

def registered_snapshot(+before: E.Snapshot, +result: H.ControlResult) -> E.Snapshot:
  E.Snapshot{E.instance(before), H.state(result), E.last_response(before), H.registry(result)}

def register_result(completed: H.ControlResult, +before: E.Snapshot, +e: G.Entry, +bytes: List<&2, U32>, send: SendReturn) -> PreparationRun:
  match completed:
    case H.ControlResult{state, entries, H.Metadata{+receipt}}:
      +actual: H.ControlResult = H.ControlResult{state, entries, H.Metadata{receipt}}
      +after = registered_snapshot(before, actual)
      push(RegistryChanged{e, before, after}, push(ReceiptConcluded{receipt, actual, after, False{}}, delivery(send, bytes, actual, after)))
    case H.ControlResult{state, entries, H.Error{status}}: error(status, before, send)

def seal_result(~c: S.Configuration, seal: SealReturn, mode: Mode, raw: P.Request,
  +before: E.Snapshot, +handle: String, +bytes: List<&2, U32>, send: SendReturn) -> PreparationRun:
  match seal:
    case SealPending{}: pending(before)
    case SealFailed{stage, identifier, fatal}: failed(stage, identifier, fatal, before, send)
    case SealSucceeded{seal}:
      +e = entry(mode, raw, E.instance(before), handle, seal)
      push(ArtifactSealed{e}, register_result(H.register(c, E.database(before), E.instance(before), e, E.registry(before)), before, e, bytes, send))

def fitting_frame(~c: S.Configuration, frame: Maybe<&2, List<&2, U32>>, mode: Mode, raw: P.Request,
  +before: E.Snapshot, +handle: String, seal: SealReturn, send: SendReturn) -> PreparationRun:
  match frame:
    case None{}: inconsistent(before)
    case Some{+bytes}:
      push(ReceiptPrepared{W.PreparedReceipt{handle}, bytes}, seal_result(c, seal, mode, raw, before, handle, bytes, send))

def receipt_fit(~c: S.Configuration, fits: Bool, mode: Mode, raw: P.Request,
  +before: E.Snapshot, +handle: String, seal: SealReturn, send: SendReturn) -> PreparationRun:
  match fits:
    case False{}: error(S.Limit{}, before, send)
    case True{}: fitting_frame(c, W.frame_receipt(W.PreparedReceipt{handle}), mode, raw, before, handle, seal, send)

def allocated(~c: S.Configuration, allocation: AllocatorReturn, mode: Mode, raw: P.Request,
  +before: E.Snapshot, seal: SealReturn, send: SendReturn) -> PreparationRun:
  match allocation:
    case AllocatorPending{}: pending(before)
    case AllocatorFailed{stage, identifier, fatal}: failed(stage, identifier, fatal, before, send)
    case AllocatorChosen{+handle}:
      push(HandleChosen{handle}, receipt_fit(c,
        R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{handle})), mode, raw, before, handle, seal, send))

def checked(~c: S.Configuration, check: CheckerReturn, +mode: Mode, +raw: P.Request, +context: D.Context,
  before: E.Snapshot, allocation: AllocatorReturn, seal: SealReturn, send: SendReturn) -> PreparationRun:
  match check:
    case CheckerPending{}: pending(before)
    case CheckerFailed{stage, identifier, fatal}: failed(stage, identifier, fatal, before, send)
    case CheckerRefuted{}: push(Refuted{W.Extension{operation(mode), raw}, context}, error(S.Certificate{}, before, send))
    case CheckerAccepted{}: push(Accepted{W.Extension{operation(mode), raw}, context}, allocated(c, allocation, mode, raw, before, seal, send))

def send_of(returns: Returns) -> SendReturn:
  Returns{check, allocation, seal, send} = returns
  send

def authenticated(~c: S.Configuration, identity: Maybe<&2, D.Context>, mode: Mode, +raw: P.Request, before: E.Snapshot, returns: Returns) -> PreparationRun:
  match identity:
    case None{}: error(S.Authentication{}, before, send_of(returns))
    case Some{context}:
      match returns:
        case Returns{check, allocation, seal, send}: checked(c, check, mode, raw, context, before, allocation, seal, send)

def run(~c: S.Configuration, +mode: Mode, +raw: P.Request, +before: E.Snapshot, returns: Returns) -> PreparationRun:
  +identity = D.authenticate(E.database(before), I.credential(raw))
  push(WireReceived{W.Extension{operation(mode), raw}},
    push(IdentityEstablished{W.Extension{operation(mode), raw}, identity}, authenticated(c, identity, mode, raw, before, returns)))

# One DATA event denotes exactly one full-observer fact. Program denotations
# are reopened from original public source only at interpretation time.
def fact(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, event: PreparationEvent) -> E.Fact:
  match event:
    case WireReceived{wire}: E.WireReceived{wire}
    case IdentityEstablished{wire, context}: E.IdentityEstablished{wire, context}
    case Accepted{+wire, context}: E.UniversalAccepted{wire, context, Source.program(binding, Host.origin(public, I.code(W.raw(wire))))}
    case Refuted{wire, context}: E.UniversalRejected{wire, context}
    case PrimitiveFailed{stage, identifier, fatal}: E.PreparedKernel{I.FailedEnvironment{stage, identifier, fatal}}
    case HandleChosen{handle}: E.HandleChosen{handle}
    case ReceiptPrepared{receipt, bytes}: E.ReceiptPrepared{receipt, bytes}
    case ArtifactSealed{+entry}: E.ArtifactSealed{entry, Source.program(binding, Host.origin(public, G.code(entry)))}
    case RegistryChanged{entry, before, after}: E.Mutated{True{}, E.Register{entry}, before, after}
    case ReceiptConcluded{receipt, result, snapshot, closes}: E.ReceiptConcluded{receipt, result, snapshot, closes}
    case ErrorPrepared{status, bytes}: E.PreparedKernel{I.Prepared{S.response_error(status), bytes}}
    case ErrorConcluded{status, snapshot, closes}: E.PreparedKernel{I.Concluded{S.response_error(status), E.database(snapshot), closes}}
    case Delivered{bytes}: E.PreparedKernel{I.DeliveredEverything{bytes}}
    case Interrupted{prefix}: E.PreparedKernel{I.DeliveryInterrupted{prefix}}
    case Closed{}: E.PreparedKernel{I.ClosedChannel{}}
