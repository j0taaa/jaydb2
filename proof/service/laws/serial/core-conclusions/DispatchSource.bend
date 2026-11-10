# Total actual dispatch source -> independent conclusion occurrence Shape.
# Every domain fact at decoded() is derived again from the ACTUAL decoder in
# the public theorem; no chosen benign prelude or completed outcome is input.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Interface.bend as I
import ../../../../../contract/PreparedLaws.bend as H
import ../../../../../contract/PreparedProtocol.bend as W
import ../../../../../contract/PreparedRegistry.bend as G
import ../../../../../contract/Protocol.bend as P
import ../../../../../contract/Resources.bend as X
import ../../../../../contract/Semantics.bend as S
import ../../../../PreparedDispatch.bend as Cached
import ../../../../HostTransitions.bend as Host
import ../../../../ProtocolService.bend as Q
import ../../../../PrimitivesService.bend as Micro
import ../../../../SourceService.bend as Source
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/PreparePhases.bend as V
import ../../../model/EventObserver.bend as O
import ../../../model/serial/Common.bend as C
import ../../../model/serial/Binding.bend as Binding
import ../../../model/serial/Decode.bend as Decode
import ../../../model/serial/DecodeEvents.bend as DecodeEvents
import ../../../model/serial/Dispatch.bend as Dispatch
import ../../../model/serial/ExecutionPhases.bend as Exec
import ../../../model/serial/ExecutionFinalWitness.bend as Frame
import ./Meaning.bend as M
import ./Algebra.bend as A
import ./ControlBase.bend as K
import ./ControlPrepare.bend as Preparation
import ./ControlInvalidate.bend as Invalidation
import ./RuntimeBase.bend as R
import ./RuntimeExecution.bend as Execution
import ./Headers.bend as Headers
import ./DecodeSafety.bend as Safe

def ordinary_bound_checker(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +origin: Source.JudgmentSyntactic, +before: E.Snapshot, +raw: P.Request, +context: D.Context, checker: V.CheckerReturn, +execution: Exec.Request, +send: V.SendReturn) ->
  M.Shape<C.events(Dispatch.ordinary_bound(c, binding, Some{origin}, before, raw, context, checker, execution, send))>:
  match checker:
    case V.CheckerPending{}: R.pending(before)
    case V.CheckerFailed{stage, identifier, fatal}: R.failed(False{}, I.code(raw), before, stage, identifier, fatal, send)
    case V.CheckerRefuted{}:
      A.prefix_run([O.BoundCore{False{}, origin, Q.Rejected{raw, context}}], C.error(False{}, I.code(raw), before, S.Certificate{}, False{}, send), {==}, R.error(False{}, I.code(raw), before, S.Certificate{}, False{}, send, Unit{}))
    case V.CheckerAccepted{}:
      A.prefix_run([O.BoundCore{False{}, origin, Q.Accepts{raw, context}}], Exec.run_bound(c, binding, origin, False{}, raw, context, before, execution, send), {==},
        Execution.run_bound(c, binding, public, origin, False{}, raw, context, before, execution, send))

def ordinary_bound(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  origin: Maybe<&2, Source.JudgmentSyntactic>, +before: E.Snapshot, +raw: P.Request, +context: D.Context, +checker: V.CheckerReturn, +execution: Exec.Request, +send: V.SendReturn) ->
  M.Shape<C.events(Dispatch.ordinary_bound(c, binding, origin, before, raw, context, checker, execution, send))>:
  match origin:
    case None{}: R.stopped(before)
    case Some{origin}: ordinary_bound_checker(c, binding, public, origin, before, raw, context, checker, execution, send)

def ordinary_checked(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +before: E.Snapshot, +raw: P.Request, +context: D.Context, +checker: V.CheckerReturn, +execution: Exec.Request, +send: V.SendReturn) ->
  M.Shape<C.events(Dispatch.ordinary_checked(c, binding, public, before, raw, context, checker, execution, send))>:
  ordinary_bound(c, binding, public, Binding.ordinary(public, raw, context), before, raw, context, checker, execution, send)

def ordinary_primitives(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +before: E.Snapshot, +raw: P.Request, +context: D.Context, primitives: Dispatch.Primitives) ->
  M.Shape<C.events(Dispatch.ordinary_identity(c, binding, public, Some{context}, before, raw, primitives))>:
  match primitives:
    case Dispatch.Primitives{checker, allocator, seal, cleanup, artifact, execution, send}: ordinary_checked(c, binding, public, before, raw, context, checker, execution, send)

def ordinary_identity(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  identity: Maybe<&2, D.Context>, +before: E.Snapshot, +raw: P.Request, +primitives: Dispatch.Primitives) ->
  M.Shape<C.events(Dispatch.ordinary_identity(c, binding, public, identity, before, raw, primitives))>:
  match identity:
    case None{}: R.error(False{}, I.code(raw), before, S.Authentication{}, False{}, Dispatch.send(primitives), Unit{})
    case Some{context}: ordinary_primitives(c, binding, public, before, raw, context, primitives)

def ordinary(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +before: E.Snapshot, +raw: P.Request, +primitives: Dispatch.Primitives) ->
  M.Shape<C.events(Dispatch.ordinary(c, binding, public, before, raw, primitives))>:
  A.prefix_run(C.core(False{}, I.code(raw), [Q.Received{raw}, Q.Authenticated{raw, D.authenticate(E.database(before), I.credential(raw))}]),
    Dispatch.ordinary_identity(c, binding, public, D.authenticate(E.database(before), I.credential(raw)), before, raw, primitives), {==},
    ordinary_identity(c, binding, public, D.authenticate(E.database(before), I.credential(raw)), before, raw, primitives))

def cached_artifact(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  artifact: Dispatch.ArtifactReturn, +before: E.Snapshot, +raw: P.Request, +entry: G.Entry, +context: D.Context, +execution: Exec.Request, +send: V.SendReturn) ->
  M.Shape<C.events(Dispatch.cached_artifact(c, binding, public, artifact, before, raw, entry, context, execution, send))>:
  match artifact:
    case Dispatch.ArtifactPending{}: R.pending(before)
    case Dispatch.ArtifactFailed{identifier, fatal}: R.failed(True{}, G.code(entry), before, X.Verify{}, identifier, fatal, send)
    case Dispatch.ArtifactAvailable{}:
      A.prefix_run([O.Resolution{raw, entry, context}], Exec.run(c, binding, public, True{}, H.resolved(raw, entry), context, before, execution, send), {==},
        Execution.run(c, binding, public, True{}, H.resolved(raw, entry), context, before, execution, send))

def cached_choice(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  choice: Cached.Choice, +before: E.Snapshot, +raw: P.Request, +artifact: Dispatch.ArtifactReturn, +execution: Exec.Request, +send: V.SendReturn) ->
  M.Shape<C.events(Dispatch.cached_choice(c, binding, public, choice, before, raw, artifact, execution, send))>:
  match choice:
    case Cached.Unauthenticated{}: R.error(True{}, "", before, S.Authentication{}, False{}, send, {==})
    case Cached.BadProof{context}: R.error(True{}, "", before, S.Input{}, False{}, send, {==})
    case Cached.Missing{context}: R.error(True{}, "", before, S.Failure{}, False{}, send, {==})
    case Cached.Selected{context, entry}: cached_artifact(c, binding, public, artifact, before, raw, entry, context, execution, send)

def cached(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +before: E.Snapshot, +raw: P.Request, +artifact: Dispatch.ArtifactReturn, +execution: Exec.Request, +send: V.SendReturn) ->
  M.Shape<C.events(Dispatch.cached(c, binding, public, before, raw, artifact, execution, send))>:
  A.prefix_run([O.Preparation{V.WireReceived{W.Extension{W.Execute{}, raw}}}, O.Preparation{V.IdentityEstablished{W.Extension{W.Execute{}, raw}, D.authenticate(E.database(before), I.credential(raw))}}],
    Dispatch.cached_choice(c, binding, public, Cached.choose(E.instance(before), Host.Published{E.database(before), E.last_response(before), E.registry(before)}, raw), before, raw, artifact, execution, send), {==},
    cached_choice(c, binding, public, Cached.choose(E.instance(before), Host.Published{E.database(before), E.last_response(before), E.registry(before)}, raw), before, raw, artifact, execution, send))

def extension(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  operation: W.Operation, +before: E.Snapshot, +raw: P.Request, primitives: Dispatch.Primitives) ->
  M.Shape<C.events(Dispatch.extension(c, binding, public, operation, before, raw, primitives))>:
  match operation primitives:
    case W.Prepare{} Dispatch.Primitives{checker, allocator, seal, cleanup, artifact, execution, send}:
      Preparation.actual_preparation_derives_all_conclusion_occurrences_and_exact_prior_framing(c, K.PreparationEmbedding{}, V.PrepareMode{}, raw, before, V.Returns{checker, allocator, seal, send})
    case W.PrepareRead{} Dispatch.Primitives{checker, allocator, seal, cleanup, artifact, execution, send}:
      Preparation.actual_preparation_derives_all_conclusion_occurrences_and_exact_prior_framing(c, K.PreparationEmbedding{}, V.ReadMode{}, raw, before, V.Returns{checker, allocator, seal, send})
    case W.Invalidate{} Dispatch.Primitives{checker, allocator, seal, cleanup, artifact, execution, send}:
      Invalidation.actual_invalidation_derives_all_conclusion_occurrences_and_exact_prior_framing(c, before, raw, cleanup, send)
    case W.Execute{} Dispatch.Primitives{checker, allocator, seal, cleanup, artifact, execution, send}: cached(c, binding, public, before, raw, artifact, execution, send)

def parsed(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +before: E.Snapshot, wire: W.WireRequest, +primitives: Dispatch.Primitives) -> M.Shape<C.events(Dispatch.parsed(c, binding, public, before, wire, primitives))>:
  match wire:
    case W.Ordinary{raw}: ordinary(c, binding, public, before, raw, primitives)
    case W.Extension{operation, raw}: extension(c, binding, public, operation, before, raw, primitives)

def decision(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  decision: Decode.Decision, +before: E.Snapshot, +primitives: Dispatch.Primitives, safe: Safe.Safe(decision)) ->
  M.Shape<C.events(Dispatch.decoded_decision(c, binding, public, decision, before, primitives))>:
  match decision:
    case Decode.Shutdown{}: R.shutdown(before)
    case Decode.TransportStopped{}: R.stopped(before)
    case Decode.Reject{mode, status, closes}: R.error(mode, "", before, status, closes, Dispatch.send(primitives), safe)
    case Decode.Parsed{wire}: parsed(c, binding, public, before, wire, primitives)

def decoded(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +before: E.Snapshot, run: Decode.DecodeRun, +primitives: Dispatch.Primitives,
  internal: Micro.Internal(Decode.frames(run)), safe: Safe.Safe(Decode.decision(run))) ->
  M.Shape<C.events(Dispatch.decoded(c, binding, public, before, run, primitives))>:
  match run:
    case Decode.DecodeRun{+selected, +frames}:
      A.prefix_run(C.core(Dispatch.decision_mode(selected), Dispatch.decision_code(selected), frames), Dispatch.decoded_decision(c, binding, public, selected, before, primitives),
        Headers.internal(Frame.Canonical{Dispatch.decision_code(selected)}, Dispatch.decision_mode(selected), frames, internal), decision(c, binding, public, selected, before, primitives, safe))

law every_actual_dispatch_derives_exact_unique_conclusion_and_its_own_prior_preparation:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +before: E.Snapshot
  for +input: X.Reception
  for +primitives: Dispatch.Primitives
  M.Shape<C.events(Dispatch.run(c, binding, public, before, input, primitives))>
def every_actual_dispatch_derives_exact_unique_conclusion_and_its_own_prior_preparation(c, binding, public, before, input, primitives):
  decoded(c, binding, public, before, Decode.run(c, E.database(before), input), primitives,
    DecodeEvents.every_actual_decode_prelude_contains_only_internal_frames(c, E.database(before), input), Safe.actual(c, E.database(before), input))
