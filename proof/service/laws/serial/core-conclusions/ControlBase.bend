# Both real embeddings of preparation events, including invalidation's lifted
# error/delivery paths. The independent Shape is recovered from source input.
import Base
import ../../../../../contract/PreparedLaws.bend as H
import ../../../../../contract/PreparedProtocol.bend as W
import ../../../../../contract/Protocol.bend as P
import ../../../../../contract/Resources.bend as X
import ../../../../../contract/Semantics.bend as S
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/PreparePhases.bend as V
import ../../../phases/InvalidationPhases.bend as N
import ../../../model/EventObserver.bend as O
import ../../../model/serial/Common.bend as C
import ./Meaning.bend as M
import ./Algebra.bend as A

type Embedding is Data:
  PreparationEmbedding{}
  InvalidationEmbedding{}

def embed(kind: Embedding, event: V.PreparationEvent) -> O.AuditEvent:
  match kind:
    case PreparationEmbedding{}: O.Preparation{event}
    case InvalidationEmbedding{}: O.Invalidation{N.InvalidationBase{event}}

def events(kind: Embedding, run: V.PreparationRun) -> List<&2, O.AuditEvent>:
  match kind:
    case PreparationEmbedding{}: C.events(C.preparation(run))
    case InvalidationEmbedding{}: C.events(C.invalidation(N.lift(run)))

def embedding_endpoint(kind: Embedding, +event: V.PreparationEvent) ->
  {M.endpoint(embed(kind, event)) == M.phase_end(event) : Maybe<&2, M.Endpoint>}:
  match kind:
    case PreparationEmbedding{}: {==}
    case InvalidationEmbedding{}: {==}

def embedding_prepared(kind: Embedding, +event: V.PreparationEvent) ->
  {M.prepared(embed(kind, event)) == M.phase_prepared(event) : Maybe<&2, M.Framing>}:
  match kind:
    case PreparationEmbedding{}: {==}
    case InvalidationEmbedding{}: {==}

def endpoint_known(+kind: Embedding, +event: V.PreparationEvent, +value: Maybe<&2, M.Endpoint>,
  actual: {M.phase_end(event) == value : Maybe<&2, M.Endpoint>}) ->
  {M.endpoint(embed(kind, event)) == value : Maybe<&2, M.Endpoint>}:
  Equal.trans(Maybe<&2, M.Endpoint>, M.endpoint(embed(kind, event)), M.phase_end(event), value, embedding_endpoint(kind, event), actual)

def prepared_known(+kind: Embedding, +event: V.PreparationEvent, +value: Maybe<&2, M.Framing>,
  actual: {M.phase_prepared(event) == value : Maybe<&2, M.Framing>}) ->
  {M.prepared(embed(kind, event)) == value : Maybe<&2, M.Framing>}:
  Equal.trans(Maybe<&2, M.Framing>, M.prepared(embed(kind, event)), M.phase_prepared(event), value, embedding_prepared(kind, event), actual)

def quiet_phase(+kind: Embedding, +event: V.PreparationEvent,
  none: {M.phase_end(event) == None{} : Maybe<&2, M.Endpoint>}) -> {M.quiet([embed(kind, event)]) == True{} : Bool}:
  A.quiet_cons(embed(kind, event), [],
    (%Equal.sym(Maybe<&2, M.Endpoint>, M.endpoint(embed(kind, event)), None{}, endpoint_known(kind, event, None{}, none)) : {M.absent(_) == True{} : Bool} {==}), {==})

def pushed_events(+kind: Embedding, +event: V.PreparationEvent, run: V.PreparationRun) ->
  {events(kind, V.push(event, run)) == Con{embed(kind, event), events(kind, run)} : List<&2, O.AuditEvent>}:
  match kind run:
    case PreparationEmbedding{} V.PreparationRun{tail, result, snapshot, waiting, closed}: {==}
    case InvalidationEmbedding{} V.PreparationRun{tail, result, snapshot, waiting, closed}: {==}

def push(+kind: Embedding, +event: V.PreparationEvent, +run: V.PreparationRun,
  none: {M.phase_end(event) == None{} : Maybe<&2, M.Endpoint>}, shape: M.Shape<events(kind, run)>) ->
  M.Shape<events(kind, V.push(event, run))>:
  %Equal.sym(List<&2, O.AuditEvent>, events(kind, V.push(event, run)), Con{embed(kind, event), events(kind, run)}, pushed_events(kind, event, run)) : M.Shape<_>
  A.prepend([embed(kind, event)], events(kind, run), quiet_phase(kind, event, none), shape)

def two_push_events(+kind: Embedding, +first: V.PreparationEvent, +second: V.PreparationEvent, run: V.PreparationRun) ->
  {events(kind, V.push(first, V.push(second, run))) == C.append([embed(kind, first)], Con{embed(kind, second), events(kind, run)}) : List<&2, O.AuditEvent>}:
  match kind run:
    case PreparationEmbedding{} V.PreparationRun{tail, result, snapshot, waiting, closed}: {==}
    case InvalidationEmbedding{} V.PreparationRun{tail, result, snapshot, waiting, closed}: {==}

def quiet_delivery(+kind: Embedding, send: V.SendReturn, +bytes: List<&2, U32>, +result: H.ControlResult, +snapshot: E.Snapshot) ->
  {M.quiet(events(kind, V.delivery(send, bytes, result, snapshot))) == True{} : Bool}:
  match kind send:
    case PreparationEmbedding{} V.SendPending{}: {==}
    case PreparationEmbedding{} V.SendComplete{}: {==}
    case PreparationEmbedding{} V.SendInterrupted{prefix}: {==}
    case InvalidationEmbedding{} V.SendPending{}: {==}
    case InvalidationEmbedding{} V.SendComplete{}: {==}
    case InvalidationEmbedding{} V.SendInterrupted{prefix}: {==}

def pending(kind: Embedding, +before: E.Snapshot) -> M.Shape<events(kind, V.pending(before))>:
  match kind:
    case PreparationEmbedding{}: M.Quiet{{==}}
    case InvalidationEmbedding{}: M.Quiet{{==}}

def inconsistent(kind: Embedding, +before: E.Snapshot) -> M.Shape<events(kind, V.inconsistent(before))>:
  match kind:
    case PreparationEmbedding{}: M.Quiet{{==}}
    case InvalidationEmbedding{}: M.Quiet{{==}}

def error_framed(+kind: Embedding, +status: S.Status, +before: E.Snapshot, +send: V.SendReturn, frame: Maybe<&2, List<&2, U32>>) ->
  M.Shape<events(kind, V.error_framed(status, before, send, frame))>:
  match frame:
    case None{}: inconsistent(kind, before)
    case Some{+bytes}:
      M.TransactionShape{[embed(kind, V.ErrorPrepared{status, bytes})],
        events(kind, V.delivery(send, bytes, H.ControlResult{E.database(before), E.registry(before), H.Error{status}}, before)),
        embed(kind, V.ErrorConcluded{status, before, False{}}), S.response_error(status), E.database(before), bytes, 0n, embed(kind, V.ErrorPrepared{status, bytes}),
        two_push_events(kind, V.ErrorPrepared{status, bytes}, V.ErrorConcluded{status, before, False{}}, V.delivery(send, bytes, H.ControlResult{E.database(before), E.registry(before), H.Error{status}}, before)),
        endpoint_known(kind, V.ErrorConcluded{status, before, False{}}, Some{M.Transaction{S.response_error(status), E.database(before), False{}}}, {==}),
        quiet_phase(kind, V.ErrorPrepared{status, bytes}, {==}), quiet_delivery(kind, send, bytes, H.ControlResult{E.database(before), E.registry(before), H.Error{status}}, before),
        {==}, prepared_known(kind, V.ErrorPrepared{status, bytes}, Some{M.Framing{S.response_error(status), bytes}}, {==})}

def error(+kind: Embedding, +status: S.Status, +before: E.Snapshot, +send: V.SendReturn) -> M.Shape<events(kind, V.error(status, before, send))>:
  error_framed(kind, status, before, send, P.frame(S.response_value(S.response_error(status))))

def failed(+kind: Embedding, +stage: X.Stage, +identifier: String, fatal: Bool, +before: E.Snapshot, +send: V.SendReturn) ->
  M.Shape<events(kind, V.failed(stage, identifier, fatal, before, send))>:
  match kind fatal:
    case PreparationEmbedding{} True{}: M.Quiet{{==}}
    case InvalidationEmbedding{} True{}: M.Quiet{{==}}
    case PreparationEmbedding{} False{}: push(PreparationEmbedding{}, V.PrimitiveFailed{stage, identifier, False{}}, V.error(S.Failure{}, before, send), {==}, error(PreparationEmbedding{}, S.Failure{}, before, send))
    case InvalidationEmbedding{} False{}: push(InvalidationEmbedding{}, V.PrimitiveFailed{stage, identifier, False{}}, V.error(S.Failure{}, before, send), {==}, error(InvalidationEmbedding{}, S.Failure{}, before, send))

def receipt(+kind: Embedding, +before: E.Snapshot, +receipt: W.Receipt, +result: H.ControlResult, +snapshot: E.Snapshot, +bytes: List<&2, U32>, +send: V.SendReturn) ->
  M.Shape<events(kind, V.push(V.ReceiptConcluded{receipt, result, snapshot, False{}}, V.delivery(send, bytes, result, snapshot)))>:
  M.MetadataShape{[], events(kind, V.delivery(send, bytes, result, snapshot)), embed(kind, V.ReceiptConcluded{receipt, result, snapshot, False{}}), receipt, result, snapshot, False{},
    pushed_events(kind, V.ReceiptConcluded{receipt, result, snapshot, False{}}, V.delivery(send, bytes, result, snapshot)),
    endpoint_known(kind, V.ReceiptConcluded{receipt, result, snapshot, False{}}, Some{M.Metadata{receipt, result, snapshot, False{}}}, {==}),
    {==}, quiet_delivery(kind, send, bytes, result, snapshot)}
