# Deterministic post-framing dispatch from physical bytes, current snapshot,
# primitive return data and a mathematical execution-prefix witness. There is
# no request/outcome table, supplied completed execution, Current or validity.
import Base
import ../../../../contract/Data.bend as D
import ../../../../contract/Interface.bend as I
import ../../../../contract/PreparedLaws.bend as H
import ../../../../contract/PreparedProtocol.bend as W
import ../../../../contract/PreparedRegistry.bend as G
import ../../../../contract/Protocol.bend as P
import ../../../../contract/Resources.bend as X
import ../../../../contract/Semantics.bend as S
import ../../../HostTransitions.bend as Host
import ../../../PreparedDispatch.bend as Cached
import ../../../ProtocolService.bend as Q
import ../../../SourceService.bend as Source
import ../../specification/ServiceLaws.bend as E
import ../../phases/PreparePhases.bend as V
import ../../phases/InvalidationPhases.bend as N
import ../EventObserver.bend as O
import ./Common.bend as C
import ./Decode.bend as Decode
import ./Binding.bend as Binding
import ./ExecutionPhases.bend as Execution

type ArtifactReturn is Data:
  ArtifactPending{}
  ArtifactAvailable{}
  ArtifactFailed{identifier: String, fatal: Bool}

type Primitives is Data:
  Primitives{checker: V.CheckerReturn, allocator: V.AllocatorReturn, seal: V.SealReturn,
    cleanup: N.CleanupReturn, artifact: ArtifactReturn, execution: Execution.Request, send: V.SendReturn}

def send(primitives: Primitives) -> V.SendReturn:
  Primitives{check, allocation, seal, cleanup, artifact, execution, send} = primitives
  send

def ordinary_bound(~c: S.Configuration, ~binding: Source.Source,
  origin: Maybe<&2, Source.JudgmentSyntactic>, +before: E.Snapshot, +raw: P.Request,
  +context: D.Context, checker: V.CheckerReturn, execution: Execution.Request, +send: V.SendReturn) -> C.CallRun:
  match origin:
    case None{}: C.stopped(before)
    case Some{+origin}:
      match checker:
        case V.CheckerPending{}: C.pending(before)
        case V.CheckerFailed{stage, identifier, fatal}: C.failed(False{}, I.code(raw), before, stage, identifier, fatal, send)
        case V.CheckerRefuted{}:
          C.prefix([O.BoundCore{False{}, origin, Q.Rejected{raw, context}}], C.error(False{}, I.code(raw), before, S.Certificate{}, False{}, send))
        case V.CheckerAccepted{}:
          C.prefix([O.BoundCore{False{}, origin, Q.Accepts{raw, context}}], Execution.run_bound(c, binding, origin, False{}, raw, context, before, execution, send))

def ordinary_checked(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +before: E.Snapshot, +raw: P.Request, +context: D.Context, checker: V.CheckerReturn,
  execution: Execution.Request, send: V.SendReturn) -> C.CallRun:
  ordinary_bound(c, binding, Binding.ordinary(public, raw, context), before, raw, context, checker, execution, send)

def ordinary_identity(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  identity: Maybe<&2, D.Context>, +before: E.Snapshot, +raw: P.Request, primitives: Primitives) -> C.CallRun:
  match identity:
    case None{}: C.error(False{}, I.code(raw), before, S.Authentication{}, False{}, send(primitives))
    case Some{context}:
      match primitives:
        case Primitives{checker, allocator, seal, cleanup, artifact, execution, send}:
          ordinary_checked(c, binding, public, before, raw, context, checker, execution, send)

def ordinary(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +before: E.Snapshot, +raw: P.Request, primitives: Primitives) -> C.CallRun:
  +identity = D.authenticate(E.database(before), I.credential(raw))
  C.prefix(C.core(False{}, I.code(raw), [Q.Received{raw}, Q.Authenticated{raw, identity}]),
    ordinary_identity(c, binding, public, identity, before, raw, primitives))

def cached_artifact(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  artifact: ArtifactReturn, +before: E.Snapshot, +raw: P.Request, +entry: G.Entry,
  +context: D.Context, execution: Execution.Request, send: V.SendReturn) -> C.CallRun:
  match artifact:
    case ArtifactPending{}: C.pending(before)
    case ArtifactFailed{identifier, fatal}: C.failed(True{}, G.code(entry), before, X.Verify{}, identifier, fatal, send)
    case ArtifactAvailable{}:
      C.prefix([O.Resolution{raw, entry, context}], Execution.run(c, binding, public, True{}, H.resolved(raw, entry), context, before, execution, send))

def cached_choice(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  choice: Cached.Choice, before: E.Snapshot, raw: P.Request, artifact: ArtifactReturn,
  execution: Execution.Request, send: V.SendReturn) -> C.CallRun:
  match choice:
    case Cached.Unauthenticated{}: C.error(True{}, "", before, S.Authentication{}, False{}, send)
    case Cached.BadProof{context}: C.error(True{}, "", before, S.Input{}, False{}, send)
    case Cached.Missing{context}: C.error(True{}, "", before, S.Failure{}, False{}, send)
    case Cached.Selected{context, entry}: cached_artifact(c, binding, public, artifact, before, raw, entry, context, execution, send)

def cached(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +before: E.Snapshot, +raw: P.Request, artifact: ArtifactReturn, execution: Execution.Request, send: V.SendReturn) -> C.CallRun:
  C.prefix([O.Preparation{V.WireReceived{W.Extension{W.Execute{}, raw}}},
      O.Preparation{V.IdentityEstablished{W.Extension{W.Execute{}, raw}, D.authenticate(E.database(before), I.credential(raw))}}],
    cached_choice(c, binding, public,
      Cached.choose(E.instance(before), Host.Published{E.database(before), E.last_response(before), E.registry(before)}, raw), before, raw, artifact, execution, send))

def extension(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  operation: W.Operation, before: E.Snapshot, raw: P.Request, primitives: Primitives) -> C.CallRun:
  match operation primitives:
    case W.Prepare{} Primitives{checker, allocator, seal, cleanup, artifact, execution, send}:
      C.preparation(V.run(c, V.PrepareMode{}, raw, before, V.Returns{checker, allocator, seal, send}))
    case W.PrepareRead{} Primitives{checker, allocator, seal, cleanup, artifact, execution, send}:
      C.preparation(V.run(c, V.ReadMode{}, raw, before, V.Returns{checker, allocator, seal, send}))
    case W.Invalidate{} Primitives{checker, allocator, seal, cleanup, artifact, execution, send}:
      C.invalidation(N.run(c, before, raw, cleanup, send))
    case W.Execute{} Primitives{checker, allocator, seal, cleanup, artifact, execution, send}:
      cached(c, binding, public, before, raw, artifact, execution, send)

def parsed(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  before: E.Snapshot, wire: W.WireRequest, primitives: Primitives) -> C.CallRun:
  match wire:
    case W.Ordinary{raw}: ordinary(c, binding, public, before, raw, primitives)
    case W.Extension{operation, raw}: extension(c, binding, public, operation, before, raw, primitives)

def decision_mode(decision: Decode.Decision) -> Bool:
  match decision:
    case Decode.Reject{mode, status, closes}: mode
    case Decode.Parsed{W.Extension{operation, raw}}: True{}
    case _: False{}

def decision_code(decision: Decode.Decision) -> String:
  match decision:
    case Decode.Parsed{wire}: I.code(W.raw(wire))
    case _: ""

def decoded_decision(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  decision: Decode.Decision, before: E.Snapshot, primitives: Primitives) -> C.CallRun:
  match decision:
    case Decode.Shutdown{}: C.shutdown(before)
    case Decode.TransportStopped{}: C.stopped(before)
    case Decode.Reject{mode, status, closes}: C.error(mode, "", before, status, closes, send(primitives))
    case Decode.Parsed{wire}: parsed(c, binding, public, before, wire, primitives)

def decoded(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +before: E.Snapshot, decoded: Decode.DecodeRun, primitives: Primitives) -> C.CallRun:
  match decoded:
    case Decode.DecodeRun{+decision, frames}:
      C.prefix(C.core(decision_mode(decision), decision_code(decision), frames), decoded_decision(c, binding, public, decision, before, primitives))

def run(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +before: E.Snapshot, input: X.Reception, primitives: Primitives) -> C.CallRun:
  decoded(c, binding, public, before, Decode.run(c, E.database(before), input), primitives)
