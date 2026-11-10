# A finite stage machine checks ALL generated prefixes, including interrupted
# and pending IO. Registration is possible only strictly after a framed
# receipt and a sealed artifact; no event can follow delivery/closure.
import Base
import ../../../contract/Data.bend as D
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
import ../specification/ServiceLaws.bend as E
import ./PreparePhases.bend as V

type Phase is Data:
  ReadyWire{}
  ReadyIdentity{}
  ReadyCheck{}
  ReadyHandle{}
  ReadyReceipt{}
  ReadySeal{}
  ReadyRegistry{}
  ReadyConclusion{}
  ReadyError{}
  ReadyErrorConclusion{}
  ReadySend{}
  ReadyClose{}
  PreparationDone{}

def advance(phase: Phase, event: V.PreparationEvent) -> Maybe<&2, Phase>:
  match phase event:
    case ReadyWire{} V.WireReceived{wire}: Some{ReadyIdentity{}}
    case ReadyIdentity{} V.IdentityEstablished{wire, context}: Some{ReadyCheck{}}
    case ReadyCheck{} V.Accepted{wire, context}: Some{ReadyHandle{}}
    case ReadyCheck{} V.Refuted{wire, context}: Some{ReadyError{}}
    case ReadyCheck{} V.PrimitiveFailed{stage, identifier, fatal}: Some{Bool.pick(Phase, fatal, ReadyClose{}, ReadyError{})}
    case ReadyHandle{} V.PrimitiveFailed{stage, identifier, fatal}: Some{Bool.pick(Phase, fatal, ReadyClose{}, ReadyError{})}
    case ReadySeal{} V.PrimitiveFailed{stage, identifier, fatal}: Some{Bool.pick(Phase, fatal, ReadyClose{}, ReadyError{})}
    case ReadyHandle{} V.HandleChosen{handle}: Some{ReadyReceipt{}}
    case ReadyReceipt{} V.ReceiptPrepared{receipt, bytes}: Some{ReadySeal{}}
    case ReadySeal{} V.ArtifactSealed{entry}: Some{ReadyRegistry{}}
    case ReadyRegistry{} V.RegistryChanged{entry, before, after}: Some{ReadyConclusion{}}
    case ReadyConclusion{} V.ReceiptConcluded{receipt, result, snapshot, closes}: Some{ReadySend{}}
    case ReadyCheck{} V.ErrorPrepared{status, bytes}: Some{ReadyErrorConclusion{}}
    case ReadyReceipt{} V.ErrorPrepared{status, bytes}: Some{ReadyErrorConclusion{}}
    case ReadyRegistry{} V.ErrorPrepared{status, bytes}: Some{ReadyErrorConclusion{}}
    case ReadyError{} V.ErrorPrepared{status, bytes}: Some{ReadyErrorConclusion{}}
    case ReadyErrorConclusion{} V.ErrorConcluded{status, snapshot, closes}: Some{ReadySend{}}
    case ReadySend{} V.Delivered{bytes}: Some{PreparationDone{}}
    case ReadySend{} V.Interrupted{prefix}: Some{ReadyClose{}}
    case ReadyClose{} V.Closed{}: Some{PreparationDone{}}
    case _ _: None{}

def following(next: Maybe<&2, Phase>, rest: Phase -> Bool) -> Bool:
  match next:
    case None{}: False{}
    case Some{phase}: rest(phase)

def ordered(events: List<&2, V.PreparationEvent>, phase: Phase) -> Bool:
  match events:
    case Nil{}: True{}
    case Con{event, rest}: following(advance(phase, event), next => ordered(rest, next))

def valid(run: V.PreparationRun, phase: Phase) -> Bool:
  ordered(V.events(run), phase)

def prepend(+event: V.PreparationEvent, +run: V.PreparationRun, +phase: Phase, +next: Phase,
  allowed: {advance(phase, event) == Some{next} : Maybe<&2, Phase>},
  later: {valid(run, next) == True{} : Bool}) ->
  {valid(V.push(event, run), phase) == True{} : Bool}:
  match run:
    case V.PreparationRun{events, result, snapshot, waiting, closed}:
      %Equal.sym(Maybe<&2, Phase>, advance(phase, event), Some{next}, allowed) :
        {following(_, next => ordered(events, next)) == True{} : Bool}
      later

def delivery_order(send: V.SendReturn, bytes: List<&2, U32>, completed: H.ControlResult, snapshot: E.Snapshot) ->
  {valid(V.delivery(send, bytes, completed, snapshot), ReadySend{}) == True{} : Bool}:
  match send:
    case V.SendPending{}: {==}
    case V.SendComplete{}: {==}
    case V.SendInterrupted{prefix}: {==}

def error_allowed(phase: Phase) -> Bool:
  match phase:
    case ReadyCheck{}: True{}
    case ReadyReceipt{}: True{}
    case ReadyRegistry{}: True{}
    case ReadyError{}: True{}
    case _: False{}

def error_step(phase: Phase, status: S.Status, bytes: List<&2, U32>, allowed: {error_allowed(phase) == True{} : Bool}) ->
  {advance(phase, V.ErrorPrepared{status, bytes}) == Some{ReadyErrorConclusion{}} : Maybe<&2, Phase>}:
  match phase:
    case ReadyCheck{}: {==}
    case ReadyReceipt{}: {==}
    case ReadyRegistry{}: {==}
    case ReadyError{}: {==}
    case ReadyWire{}: F.absurd_boolean({advance(ReadyWire{}, V.ErrorPrepared{status, bytes}) == Some{ReadyErrorConclusion{}} : Maybe<&2, Phase>}, allowed)
    case ReadyIdentity{}: F.absurd_boolean({advance(ReadyIdentity{}, V.ErrorPrepared{status, bytes}) == Some{ReadyErrorConclusion{}} : Maybe<&2, Phase>}, allowed)
    case ReadyHandle{}: F.absurd_boolean({advance(ReadyHandle{}, V.ErrorPrepared{status, bytes}) == Some{ReadyErrorConclusion{}} : Maybe<&2, Phase>}, allowed)
    case ReadySeal{}: F.absurd_boolean({advance(ReadySeal{}, V.ErrorPrepared{status, bytes}) == Some{ReadyErrorConclusion{}} : Maybe<&2, Phase>}, allowed)
    case ReadyConclusion{}: F.absurd_boolean({advance(ReadyConclusion{}, V.ErrorPrepared{status, bytes}) == Some{ReadyErrorConclusion{}} : Maybe<&2, Phase>}, allowed)
    case ReadyErrorConclusion{}: F.absurd_boolean({advance(ReadyErrorConclusion{}, V.ErrorPrepared{status, bytes}) == Some{ReadyErrorConclusion{}} : Maybe<&2, Phase>}, allowed)
    case ReadySend{}: F.absurd_boolean({advance(ReadySend{}, V.ErrorPrepared{status, bytes}) == Some{ReadyErrorConclusion{}} : Maybe<&2, Phase>}, allowed)
    case ReadyClose{}: F.absurd_boolean({advance(ReadyClose{}, V.ErrorPrepared{status, bytes}) == Some{ReadyErrorConclusion{}} : Maybe<&2, Phase>}, allowed)
    case PreparationDone{}: F.absurd_boolean({advance(PreparationDone{}, V.ErrorPrepared{status, bytes}) == Some{ReadyErrorConclusion{}} : Maybe<&2, Phase>}, allowed)

def error_framed_order(+status: S.Status, +snapshot: E.Snapshot, +send: V.SendReturn,
  frame: Maybe<&2, List<&2, U32>>, +phase: Phase, allowed: {error_allowed(phase) == True{} : Bool}) ->
  {valid(V.error_framed(status, snapshot, send, frame), phase) == True{} : Bool}:
  match frame:
    case None{}: {==}
    case Some{+bytes}:
      prepend(V.ErrorPrepared{status, bytes},
        V.push(V.ErrorConcluded{status, snapshot, False{}}, V.delivery(send, bytes,
          H.ControlResult{E.database(snapshot), E.registry(snapshot), H.Error{status}}, snapshot)),
        phase, ReadyErrorConclusion{}, error_step(phase, status, bytes, allowed),
        prepend(V.ErrorConcluded{status, snapshot, False{}}, V.delivery(send, bytes,
          H.ControlResult{E.database(snapshot), E.registry(snapshot), H.Error{status}}, snapshot),
          ReadyErrorConclusion{}, ReadySend{}, {==},
          delivery_order(send, bytes, H.ControlResult{E.database(snapshot), E.registry(snapshot), H.Error{status}}, snapshot)))

def error_order(+status: S.Status, +snapshot: E.Snapshot, +send: V.SendReturn,
  +phase: Phase, allowed: {error_allowed(phase) == True{} : Bool}) ->
  {valid(V.error(status, snapshot, send), phase) == True{} : Bool}:
  error_framed_order(status, snapshot, send, P.frame(S.response_value(S.response_error(status))), phase, allowed)

def primitive_allowed(phase: Phase) -> Bool:
  match phase:
    case ReadyCheck{}: True{}
    case ReadyHandle{}: True{}
    case ReadySeal{}: True{}
    case _: False{}

def primitive_step(phase: Phase, stage: X.Stage, identifier: String, fatal: Bool,
  allowed: {primitive_allowed(phase) == True{} : Bool}) ->
  {advance(phase, V.PrimitiveFailed{stage, identifier, fatal}) == Some{Bool.pick(Phase, fatal, ReadyClose{}, ReadyError{})} : Maybe<&2, Phase>}:
  match phase:
    case ReadyCheck{}: {==}
    case ReadyHandle{}: {==}
    case ReadySeal{}: {==}
    case ReadyWire{}: F.absurd_boolean({advance(ReadyWire{}, V.PrimitiveFailed{stage, identifier, fatal}) == Some{Bool.pick(Phase, fatal, ReadyClose{}, ReadyError{})} : Maybe<&2, Phase>}, allowed)
    case ReadyIdentity{}: F.absurd_boolean({advance(ReadyIdentity{}, V.PrimitiveFailed{stage, identifier, fatal}) == Some{Bool.pick(Phase, fatal, ReadyClose{}, ReadyError{})} : Maybe<&2, Phase>}, allowed)
    case ReadyReceipt{}: F.absurd_boolean({advance(ReadyReceipt{}, V.PrimitiveFailed{stage, identifier, fatal}) == Some{Bool.pick(Phase, fatal, ReadyClose{}, ReadyError{})} : Maybe<&2, Phase>}, allowed)
    case ReadyRegistry{}: F.absurd_boolean({advance(ReadyRegistry{}, V.PrimitiveFailed{stage, identifier, fatal}) == Some{Bool.pick(Phase, fatal, ReadyClose{}, ReadyError{})} : Maybe<&2, Phase>}, allowed)
    case ReadyConclusion{}: F.absurd_boolean({advance(ReadyConclusion{}, V.PrimitiveFailed{stage, identifier, fatal}) == Some{Bool.pick(Phase, fatal, ReadyClose{}, ReadyError{})} : Maybe<&2, Phase>}, allowed)
    case ReadyError{}: F.absurd_boolean({advance(ReadyError{}, V.PrimitiveFailed{stage, identifier, fatal}) == Some{Bool.pick(Phase, fatal, ReadyClose{}, ReadyError{})} : Maybe<&2, Phase>}, allowed)
    case ReadyErrorConclusion{}: F.absurd_boolean({advance(ReadyErrorConclusion{}, V.PrimitiveFailed{stage, identifier, fatal}) == Some{Bool.pick(Phase, fatal, ReadyClose{}, ReadyError{})} : Maybe<&2, Phase>}, allowed)
    case ReadySend{}: F.absurd_boolean({advance(ReadySend{}, V.PrimitiveFailed{stage, identifier, fatal}) == Some{Bool.pick(Phase, fatal, ReadyClose{}, ReadyError{})} : Maybe<&2, Phase>}, allowed)
    case ReadyClose{}: F.absurd_boolean({advance(ReadyClose{}, V.PrimitiveFailed{stage, identifier, fatal}) == Some{Bool.pick(Phase, fatal, ReadyClose{}, ReadyError{})} : Maybe<&2, Phase>}, allowed)
    case PreparationDone{}: F.absurd_boolean({advance(PreparationDone{}, V.PrimitiveFailed{stage, identifier, fatal}) == Some{Bool.pick(Phase, fatal, ReadyClose{}, ReadyError{})} : Maybe<&2, Phase>}, allowed)

def failed_order(+stage: X.Stage, +identifier: String, fatal: Bool,
  +snapshot: E.Snapshot, +send: V.SendReturn, +phase: Phase, allowed: {primitive_allowed(phase) == True{} : Bool}) ->
  {valid(V.failed(stage, identifier, fatal, snapshot, send), phase) == True{} : Bool}:
  match fatal:
    case True{}:
      prepend(V.PrimitiveFailed{stage, identifier, True{}},
        V.PreparationRun{[V.Closed{}], None{}, snapshot, False{}, True{}},
        phase, ReadyClose{}, primitive_step(phase, stage, identifier, True{}, allowed), {==})
    case False{}:
      prepend(V.PrimitiveFailed{stage, identifier, False{}}, V.error(S.Failure{}, snapshot, send),
        phase, ReadyError{}, primitive_step(phase, stage, identifier, False{}, allowed),
        error_order(S.Failure{}, snapshot, send, ReadyError{}, {==}))

def registered_order(completed: H.ControlResult, +before: E.Snapshot, +entry: G.Entry,
  +bytes: List<&2, U32>, +send: V.SendReturn) ->
  {valid(V.register_result(completed, before, entry, bytes, send), ReadyRegistry{}) == True{} : Bool}:
  match completed:
    case H.ControlResult{state, entries, H.Metadata{+receipt}}:
      +actual: H.ControlResult = H.ControlResult{state, entries, H.Metadata{receipt}}
      +after = V.registered_snapshot(before, actual)
      prepend(V.RegistryChanged{entry, before, after},
        V.push(V.ReceiptConcluded{receipt, actual, after, False{}}, V.delivery(send, bytes, actual, after)),
        ReadyRegistry{}, ReadyConclusion{}, {==},
        prepend(V.ReceiptConcluded{receipt, actual, after, False{}}, V.delivery(send, bytes, actual, after),
          ReadyConclusion{}, ReadySend{}, {==}, delivery_order(send, bytes, actual, after)))
    case H.ControlResult{state, entries, H.Error{status}}:
      error_order(status, before, send, ReadyRegistry{}, {==})

def seal_order(~c: S.Configuration, seal: V.SealReturn, +mode: V.Mode, +raw: P.Request,
  +before: E.Snapshot, +handle: String, +bytes: List<&2, U32>, +send: V.SendReturn) ->
  {valid(V.seal_result(c, seal, mode, raw, before, handle, bytes, send), ReadySeal{}) == True{} : Bool}:
  match seal:
    case V.SealPending{}: {==}
    case V.SealFailed{stage, identifier, fatal}: failed_order(stage, identifier, fatal, before, send, ReadySeal{}, {==})
    case V.SealSucceeded{seal}:
      +entry = V.entry(mode, raw, E.instance(before), handle, seal)
      prepend(V.ArtifactSealed{entry},
        V.register_result(H.register(c, E.database(before), E.instance(before), entry, E.registry(before)), before, entry, bytes, send),
        ReadySeal{}, ReadyRegistry{}, {==},
        registered_order(H.register(c, E.database(before), E.instance(before), entry, E.registry(before)), before, entry, bytes, send))

def framed_order(~c: S.Configuration, frame: Maybe<&2, List<&2, U32>>, +mode: V.Mode, +raw: P.Request,
  +before: E.Snapshot, +handle: String, +seal: V.SealReturn, +send: V.SendReturn) ->
  {valid(V.fitting_frame(c, frame, mode, raw, before, handle, seal, send), ReadyReceipt{}) == True{} : Bool}:
  match frame:
    case None{}: {==}
    case Some{+bytes}:
      prepend(V.ReceiptPrepared{W.PreparedReceipt{handle}, bytes}, V.seal_result(c, seal, mode, raw, before, handle, bytes, send),
        ReadyReceipt{}, ReadySeal{}, {==}, seal_order(c, seal, mode, raw, before, handle, bytes, send))

def receipt_order(~c: S.Configuration, fits: Bool, +mode: V.Mode, +raw: P.Request,
  +before: E.Snapshot, +handle: String, +seal: V.SealReturn, +send: V.SendReturn) ->
  {valid(V.receipt_fit(c, fits, mode, raw, before, handle, seal, send), ReadyReceipt{}) == True{} : Bool}:
  match fits:
    case False{}: error_order(S.Limit{}, before, send, ReadyReceipt{}, {==})
    case True{}: framed_order(c, W.frame_receipt(W.PreparedReceipt{handle}), mode, raw, before, handle, seal, send)

def allocation_order(~c: S.Configuration, allocation: V.AllocatorReturn, +mode: V.Mode, +raw: P.Request,
  +before: E.Snapshot, +seal: V.SealReturn, +send: V.SendReturn) ->
  {valid(V.allocated(c, allocation, mode, raw, before, seal, send), ReadyHandle{}) == True{} : Bool}:
  match allocation:
    case V.AllocatorPending{}: {==}
    case V.AllocatorFailed{stage, identifier, fatal}: failed_order(stage, identifier, fatal, before, send, ReadyHandle{}, {==})
    case V.AllocatorChosen{+handle}:
      prepend(V.HandleChosen{handle},
        V.receipt_fit(c, R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{handle})), mode, raw, before, handle, seal, send),
        ReadyHandle{}, ReadyReceipt{}, {==},
        receipt_order(c, R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{handle})), mode, raw, before, handle, seal, send))

def checker_order(~c: S.Configuration, check: V.CheckerReturn, +mode: V.Mode, +raw: P.Request, +context: D.Context,
  +before: E.Snapshot, +allocation: V.AllocatorReturn, +seal: V.SealReturn, +send: V.SendReturn) ->
  {valid(V.checked(c, check, mode, raw, context, before, allocation, seal, send), ReadyCheck{}) == True{} : Bool}:
  match check:
    case V.CheckerPending{}: {==}
    case V.CheckerFailed{stage, identifier, fatal}: failed_order(stage, identifier, fatal, before, send, ReadyCheck{}, {==})
    case V.CheckerRefuted{}:
      prepend(V.Refuted{W.Extension{V.operation(mode), raw}, context}, V.error(S.Certificate{}, before, send),
        ReadyCheck{}, ReadyError{}, {==}, error_order(S.Certificate{}, before, send, ReadyError{}, {==}))
    case V.CheckerAccepted{}:
      prepend(V.Accepted{W.Extension{V.operation(mode), raw}, context}, V.allocated(c, allocation, mode, raw, before, seal, send),
        ReadyCheck{}, ReadyHandle{}, {==}, allocation_order(c, allocation, mode, raw, before, seal, send))

def authentication_order(~c: S.Configuration, identity: Maybe<&2, D.Context>, +mode: V.Mode, +raw: P.Request,
  +before: E.Snapshot, +returns: V.Returns) ->
  {valid(V.authenticated(c, identity, mode, raw, before, returns), ReadyCheck{}) == True{} : Bool}:
  match identity:
    case None{}: error_order(S.Authentication{}, before, V.send_of(returns), ReadyCheck{}, {==})
    case Some{context}:
      match returns:
        case V.Returns{check, allocation, seal, send}: checker_order(c, check, mode, raw, context, before, allocation, seal, send)

law every_actual_preparation_prefix_follows_strict_stage_order:
  for ~c: S.Configuration
  for +mode: V.Mode
  for +raw: P.Request
  for +before: E.Snapshot
  for +returns: V.Returns
  {valid(V.run(c, mode, raw, before, returns), ReadyWire{}) == True{} : Bool}
def every_actual_preparation_prefix_follows_strict_stage_order(c, mode, raw, before, returns):
  +identity = D.authenticate(E.database(before), I.credential(raw))
  prepend(V.WireReceived{W.Extension{V.operation(mode), raw}},
    V.push(V.IdentityEstablished{W.Extension{V.operation(mode), raw}, identity}, V.authenticated(c, identity, mode, raw, before, returns)),
    ReadyWire{}, ReadyIdentity{}, {==},
    prepend(V.IdentityEstablished{W.Extension{V.operation(mode), raw}, identity}, V.authenticated(c, identity, mode, raw, before, returns),
      ReadyIdentity{}, ReadyCheck{}, {==}, authentication_order(c, identity, mode, raw, before, returns)))
