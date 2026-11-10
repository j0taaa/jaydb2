# Decoder primitive frames and actual finite execution headers cannot contain
# a prepared transaction or metadata conclusion. No completed trace is input.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Interface.bend as I
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/Protocol.bend as P
import ../../../../../contract/Semantics.bend as S
import ../../../../Foundations.bend as F
import ../../../../ProtocolService.bend as Q
import ../../../../PrimitivesService.bend as Micro
import ../../../../SourceService.bend as Source
import ../../../../ExecutionService.bend as Adapter
import ../../../../../src/Core.bend as Core
import ../../../model/EventObserver.bend as O
import ../../../model/serial/ExecutionFinalWitness.bend as W
import ./Meaning.bend as M
import ./Algebra.bend as A

def frame_endpoint(kind: W.Framing, +mode: Bool, +frame: Q.Frame) ->
  {M.endpoint(W.frame(kind, mode, frame)) == M.frame_end(mode, frame) : Maybe<&2, M.Endpoint>}:
  match kind:
    case W.Canonical{code}: {==}
    case W.Bound{origin}: {==}

def frames_cons(kind: W.Framing, +mode: Bool, +frame: Q.Frame, +tail: List<&2, Q.Frame>) ->
  {W.frames(kind, mode, Con{frame, tail}) == Con{W.frame(kind, mode, frame), W.frames(kind, mode, tail)} : List<&2, O.AuditEvent>}:
  match kind:
    case W.Canonical{code}: {==}
    case W.Bound{origin}: {==}

def quiet_nil(kind: W.Framing, +mode: Bool) -> {M.quiet(W.frames(kind, mode, [])) == True{} : Bool}:
  match kind:
    case W.Canonical{code}: {==}
    case W.Bound{origin}: {==}

def quiet_cons(+kind: W.Framing, +mode: Bool, +frame: Q.Frame, +tail: List<&2, Q.Frame>,
  none: {M.frame_end(mode, frame) == None{} : Maybe<&2, M.Endpoint>}, quiet: {M.quiet(W.frames(kind, mode, tail)) == True{} : Bool}) ->
  {M.quiet(W.frames(kind, mode, Con{frame, tail})) == True{} : Bool}:
  %Equal.sym(List<&2, O.AuditEvent>, W.frames(kind, mode, Con{frame, tail}), Con{W.frame(kind, mode, frame), W.frames(kind, mode, tail)}, frames_cons(kind, mode, frame, tail)) : {M.quiet(_) == True{} : Bool}
  A.quiet_cons(W.frame(kind, mode, frame), W.frames(kind, mode, tail),
    (%Equal.sym(Maybe<&2, M.Endpoint>, M.endpoint(W.frame(kind, mode, frame)), None{}, Equal.trans(Maybe<&2, M.Endpoint>, M.endpoint(W.frame(kind, mode, frame)), M.frame_end(mode, frame), None{}, frame_endpoint(kind, mode, frame), none)) : {M.absent(_) == True{} : Bool} {==}), quiet)

def internal_frame(+mode: Bool, frame: Q.Frame, inside: {Micro.internal(frame) == True{} : Bool}) ->
  {M.frame_end(mode, frame) == None{} : Maybe<&2, M.Endpoint>}:
  match frame:
    case Q.Configured{}: {==}
    case Q.InitialAccepts{}: {==}
    case Q.Initialized{state}: {==}
    case Q.InitialRefused{status}: {==}
    case Q.Encoded{value, bytes}: {==}
    case Q.Decoded{bytes, value}: {==}
    case Q.Stored{state, bytes, abstraction}: {==}
    case Q.Checked{position, count}: {==}
    case Q.Constructed{position, count}: {==}
    case Q.Read{before, count, declared}: {==}
    case Q.Received{request}: {==}
    case Q.Authenticated{request, context}: {==}
    case Q.Accepts{request, context}: {==}
    case Q.Rejected{request, context}: {==}
    case Q.Started{request, context}: {==}
    case Q.Evaluated{request, context, execution_trace}: {==}
    case Q.Operated{schema, state, operation, result}: {==}
    case Q.Prepared{response, bytes}: {==}
    case Q.Published{state}: {==}
    case Q.Visible{state}: {==}
    case Q.Failed{stage, identifier, fatal}: {==}
    case Q.Completed{response, state, closes}: L.ex_false({M.frame_end(mode, Q.Completed{response, state, closes}) == None{} : Maybe<&2, M.Endpoint>}, F.false_negative_true(inside))
    case Q.Delivered{bytes}: {==}
    case Q.Interrupted{prefix}: {==}
    case Q.Closed{}: {==}
    case Q.Next{previous, initial}: {==}
    case Q.Inspection{description}: {==}
    case Q.Effect{description}: {==}


def internal(+kind: W.Framing, +mode: Bool, frames: List<&2, Q.Frame>, inside: Micro.Internal(frames)) ->
  {M.quiet(W.frames(kind, mode, frames)) == True{} : Bool}:
  match frames inside:
    case Nil{} unit: quiet_nil(kind, mode)
    case Con{+head, +tail} L.Both{first, rest}:
      quiet_cons(kind, mode, head, tail, internal_frame(mode, head, first), internal(kind, mode, tail, rest))

def expanded(+kind: W.Framing, +mode: Bool, +request: P.Request, +context: D.Context, frames: List<&2, Q.FrameExec>) ->
  {M.quiet(W.frames(kind, mode, Q.expand_exec(request, context, frames))) == True{} : Bool}:
  match frames:
    case Nil{}: quiet_nil(kind, mode)
    case Con{Q.Evaluation{+trace}, +tail}:
      quiet_cons(kind, mode, Q.Evaluated{request, context, trace}, Q.expand_exec(request, context, tail), {==}, expanded(kind, mode, request, context, tail))
    case Con{Q.Operation{+schema, +state, +operation, +result}, +tail}:
      quiet_cons(kind, mode, Q.Operated{schema, state, operation, result}, Q.expand_exec(request, context, tail), {==}, expanded(kind, mode, request, context, tail))

def header(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +kind: W.Framing,
  +mode: Bool, +request: P.Request, +context: D.Context, +before: D.State, +steps: Nat) ->
  {M.quiet(W.header(c, binding, public, kind, mode, request, context, before, steps)) == True{} : Bool}:
  quiet_cons(kind, mode, Q.Started{request, context}, Q.expand_exec(request, context, Adapter.generate(steps, Core.start(Source.program(binding, W.origin(public, kind)), context, I.arguments(request), before), S.schema(c))), {==},
    expanded(kind, mode, request, context, Adapter.generate(steps, Core.start(Source.program(binding, W.origin(public, kind)), context, I.arguments(request), before), S.schema(c))))
