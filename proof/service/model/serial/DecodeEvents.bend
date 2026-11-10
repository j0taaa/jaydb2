# The ACTUAL decode renderer supplies only checked codec/internal facts. No
# caller-selected arbitrary frame prefix is assumed to be benign.
import Base
import ../../../../contract/Bytes.bend as Bytes
import ../../../../contract/Data.bend as D
import ../../../../contract/Interface.bend as I
import ../../../../contract/Logic.bend as L
import ../../../../contract/PreparedProtocol.bend as W
import ../../../../contract/Requirements.bend as R
import ../../../../contract/Resources.bend as X
import ../../../../contract/Semantics.bend as S
import ../../../Foundations.bend as F
import ../../../PrimitivesService.bend as Micro
import ../../../ProtocolService.bend as Q
import ../../../SourceService.bend as Source
import ../../../HostTransitions.bend as Host
import ../../specification/ServiceLaws.bend as E
import ../ObservationUniqueness.bend as U
import ./Common.bend as C
import ./Engine.bend as Engine
import ../FrameBounds.bend as B
import ./Decode.bend as Decode


def limited(limit: Maybe<&2, Bytes.Number64>, current: D.State, operation: Maybe<&2, W.Operation>, +bytes: List<&2, U32>) ->
  Micro.Internal(Decode.frames(Decode.limited(limit, current, operation, bytes))):
  match limit:
    case None{}: Unit{}
    case Some{+ceiling}: Micro.expand_internal(Micro.Decode{bytes, ceiling})


def routed(~c: S.Configuration, current: D.State, route: W.Dispatch) -> Micro.Internal(Decode.frames(Decode.routed(c, current, route))):
  match route:
    case W.InvalidExtension{}: Unit{}
    case W.OrdinaryBody{bytes}: limited(Bytes.nat64(R.limit_message(S.limits(c))), current, None{}, bytes)
    case W.ExtensionBody{operation, bytes}: limited(Bytes.nat64(R.limit_message(S.limits(c))), current, Some{operation}, bytes)


def disposed(~c: S.Configuration, current: D.State, disposition: X.Disposition) -> Micro.Internal(Decode.frames(Decode.disposed(c, current, disposition))):
  match disposition:
    case X.CloseWithoutResponse{}: Unit{}
    case X.RefuseClose{status}: Unit{}
    case X.RefuseContinue{status}: Unit{}
    case X.ProcessBody{bytes}: routed(c, current, W.route_dispatch(bytes))


law every_actual_decode_prelude_contains_only_internal_frames:
  for ~c: S.Configuration
  for current: D.State
  for input: X.Reception
  Micro.Internal(Decode.frames(Decode.run(c, current, input)))
def every_actual_decode_prelude_contains_only_internal_frames(c, current, input):
  disposed(c, current, X.decide_reception(c, input))


def InternalFact(fact: I.Fact) -> Type:
  match fact:
    case I.Encoded{value, bytes}: Unit
    case I.Decoded{bytes, value}: Unit
    case I.Stored{state, bytes, abstraction}: Unit
    case I.CheckedLength{position, count}: Unit
    case I.AllocatedField{position, count}: Unit
    case I.ReadBody{before, count, declared}: Unit
    case _: Empty


def query_internal(frames: List<&2, Q.Frame>, index: Nat, -frame: Q.Frame,
  all: Micro.Internal(frames), found: {B.query(Q.Frame, frames, index) == Some{frame} : Maybe<&2, Q.Frame>}) ->
  {Micro.internal(frame) == True{} : Bool}:
  match frames index all:
    case Nil{} _ _: L.ex_false({Micro.internal(frame) == True{} : Bool}, F.none_negative_some(Q.Frame, frame, found))
    case Con{head, rest} 0n L.Both{first, later}:
      %F.some_injective(Q.Frame, head, frame, found) : {Micro.internal(_) == True{} : Bool}
      first
    case Con{head, rest} 1n+k L.Both{first, later}: query_internal(rest, k, frame, later, found)


def internal_frame_fact(~c: S.Configuration, -program: S.Program, +frame: Q.Frame, inside: {Micro.internal(frame) == True{} : Bool}) ->
  InternalFact(Q.fact_of_frame(c, program, frame)):
  match frame:
    case Q.Configured{}: L.ex_false(InternalFact(Q.fact_of_frame(c, program, Q.Configured{})), F.false_negative_true(inside))
    case Q.InitialAccepts{}: L.ex_false(InternalFact(Q.fact_of_frame(c, program, Q.InitialAccepts{})), F.false_negative_true(inside))
    case Q.Initialized{state}: L.ex_false(InternalFact(Q.fact_of_frame(c, program, Q.Initialized{state})), F.false_negative_true(inside))
    case Q.InitialRefused{status}: L.ex_false(InternalFact(Q.fact_of_frame(c, program, Q.InitialRefused{status})), F.false_negative_true(inside))
    case Q.Encoded{value, bytes}: Unit{}
    case Q.Decoded{bytes, value}: Unit{}
    case Q.Stored{state, bytes, abstraction}: Unit{}
    case Q.Checked{position, count}: Unit{}
    case Q.Constructed{position, count}: Unit{}
    case Q.Read{before, count, declared}: Unit{}
    case Q.Received{request}: L.ex_false(InternalFact(Q.fact_of_frame(c, program, Q.Received{request})), F.false_negative_true(inside))
    case Q.Authenticated{request, context}: L.ex_false(InternalFact(Q.fact_of_frame(c, program, Q.Authenticated{request, context})), F.false_negative_true(inside))
    case Q.Accepts{request, context}: L.ex_false(InternalFact(Q.fact_of_frame(c, program, Q.Accepts{request, context})), F.false_negative_true(inside))
    case Q.Rejected{request, context}: L.ex_false(InternalFact(Q.fact_of_frame(c, program, Q.Rejected{request, context})), F.false_negative_true(inside))
    case Q.Started{request, context}: L.ex_false(InternalFact(Q.fact_of_frame(c, program, Q.Started{request, context})), F.false_negative_true(inside))
    case Q.Evaluated{request, context, execution_trace}: L.ex_false(InternalFact(Q.fact_of_frame(c, program, Q.Evaluated{request, context, execution_trace})), F.false_negative_true(inside))
    case Q.Operated{schema, state, operation, result}: L.ex_false(InternalFact(Q.fact_of_frame(c, program, Q.Operated{schema, state, operation, result})), F.false_negative_true(inside))
    case Q.Prepared{response, bytes}: L.ex_false(InternalFact(Q.fact_of_frame(c, program, Q.Prepared{response, bytes})), F.false_negative_true(inside))
    case Q.Published{state}: L.ex_false(InternalFact(Q.fact_of_frame(c, program, Q.Published{state})), F.false_negative_true(inside))
    case Q.Visible{state}: L.ex_false(InternalFact(Q.fact_of_frame(c, program, Q.Visible{state})), F.false_negative_true(inside))
    case Q.Failed{stage, identifier, fatal}: L.ex_false(InternalFact(Q.fact_of_frame(c, program, Q.Failed{stage, identifier, fatal})), F.false_negative_true(inside))
    case Q.Completed{response, state, closes}: L.ex_false(InternalFact(Q.fact_of_frame(c, program, Q.Completed{response, state, closes})), F.false_negative_true(inside))
    case Q.Delivered{bytes}: L.ex_false(InternalFact(Q.fact_of_frame(c, program, Q.Delivered{bytes})), F.false_negative_true(inside))
    case Q.Interrupted{prefix}: L.ex_false(InternalFact(Q.fact_of_frame(c, program, Q.Interrupted{prefix})), F.false_negative_true(inside))
    case Q.Closed{}: L.ex_false(InternalFact(Q.fact_of_frame(c, program, Q.Closed{})), F.false_negative_true(inside))
    case Q.Next{previous, initial}: L.ex_false(InternalFact(Q.fact_of_frame(c, program, Q.Next{previous, initial})), F.false_negative_true(inside))
    case Q.Inspection{description}: L.ex_false(InternalFact(Q.fact_of_frame(c, program, Q.Inspection{description})), F.false_negative_true(inside))
    case Q.Effect{description}: L.ex_false(InternalFact(Q.fact_of_frame(c, program, Q.Effect{description})), F.false_negative_true(inside))


law every_actual_decode_frame_query_has_only_a_core_internal_fact:
  for ~c: S.Configuration
  for -program: S.Program
  for +current: D.State
  for +input: X.Reception
  for +index: Nat
  for +frame: Q.Frame
  for found: {B.query(Q.Frame, Decode.frames(Decode.run(c, current, input)), index) == Some{frame} : Maybe<&2, Q.Frame>}
  InternalFact(Q.fact_of_frame(c, program, frame))
def every_actual_decode_frame_query_has_only_a_core_internal_fact(c, program, current, input, index, frame, found):
  internal_frame_fact(c, program, frame, query_internal(Decode.frames(Decode.run(c, current, input)), index, frame,
    every_actual_decode_prelude_contains_only_internal_frames(c, current, input), found))


def internal_facts_cannot_be_conclusions(-fact: I.Fact, -response: S.Response, -state: D.State, -closes: Bool,
  internal: InternalFact(fact), claimed: {fact == I.Concluded{response, state, closes} : I.Fact}) -> Empty:
  %claimed : InternalFact(_)
  internal


def internal_frame_has_no_service_view(~c: S.Configuration, -program: S.Program, mode: Bool, +frame: Q.Frame,
  inside: {Micro.internal(frame) == True{} : Bool}) ->
  {U.view(E.core_fact(mode, Q.fact_of_frame(c, program, frame))) == U.VoidView{} : U.View}:
  match mode frame:
    case False{} Q.Configured{}: L.ex_false({U.view(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Configured{}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case False{} Q.InitialAccepts{}: L.ex_false({U.view(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.InitialAccepts{}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case False{} Q.Initialized{state}: L.ex_false({U.view(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Initialized{state}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case False{} Q.InitialRefused{status}: L.ex_false({U.view(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.InitialRefused{status}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case False{} Q.Encoded{value, bytes}: {==}
    case False{} Q.Decoded{bytes, value}: {==}
    case False{} Q.Stored{state, bytes, abstraction}: {==}
    case False{} Q.Checked{position, count}: {==}
    case False{} Q.Constructed{position, count}: {==}
    case False{} Q.Read{before, count, declared}: {==}
    case False{} Q.Received{request}: L.ex_false({U.view(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Received{request}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case False{} Q.Authenticated{request, context}: L.ex_false({U.view(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Authenticated{request, context}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case False{} Q.Accepts{request, context}: L.ex_false({U.view(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Accepts{request, context}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case False{} Q.Rejected{request, context}: L.ex_false({U.view(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Rejected{request, context}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case False{} Q.Started{request, context}: L.ex_false({U.view(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Started{request, context}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case False{} Q.Evaluated{request, context, execution_trace}: L.ex_false({U.view(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Evaluated{request, context, execution_trace}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case False{} Q.Operated{schema, state, operation, result}: L.ex_false({U.view(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Operated{schema, state, operation, result}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case False{} Q.Prepared{response, bytes}: L.ex_false({U.view(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Prepared{response, bytes}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case False{} Q.Published{state}: L.ex_false({U.view(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Published{state}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case False{} Q.Visible{state}: L.ex_false({U.view(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Visible{state}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case False{} Q.Failed{stage, identifier, fatal}: L.ex_false({U.view(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Failed{stage, identifier, fatal}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case False{} Q.Completed{response, state, closes}: L.ex_false({U.view(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Completed{response, state, closes}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case False{} Q.Delivered{bytes}: L.ex_false({U.view(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Delivered{bytes}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case False{} Q.Interrupted{prefix}: L.ex_false({U.view(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Interrupted{prefix}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case False{} Q.Closed{}: L.ex_false({U.view(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Closed{}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case False{} Q.Next{previous, initial}: L.ex_false({U.view(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Next{previous, initial}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case False{} Q.Inspection{description}: L.ex_false({U.view(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Inspection{description}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case False{} Q.Effect{description}: L.ex_false({U.view(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Effect{description}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case True{} Q.Configured{}: L.ex_false({U.view(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Configured{}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case True{} Q.InitialAccepts{}: L.ex_false({U.view(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.InitialAccepts{}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case True{} Q.Initialized{state}: L.ex_false({U.view(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Initialized{state}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case True{} Q.InitialRefused{status}: L.ex_false({U.view(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.InitialRefused{status}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case True{} Q.Encoded{value, bytes}: {==}
    case True{} Q.Decoded{bytes, value}: {==}
    case True{} Q.Stored{state, bytes, abstraction}: {==}
    case True{} Q.Checked{position, count}: {==}
    case True{} Q.Constructed{position, count}: {==}
    case True{} Q.Read{before, count, declared}: {==}
    case True{} Q.Received{request}: L.ex_false({U.view(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Received{request}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case True{} Q.Authenticated{request, context}: L.ex_false({U.view(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Authenticated{request, context}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case True{} Q.Accepts{request, context}: L.ex_false({U.view(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Accepts{request, context}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case True{} Q.Rejected{request, context}: L.ex_false({U.view(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Rejected{request, context}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case True{} Q.Started{request, context}: L.ex_false({U.view(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Started{request, context}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case True{} Q.Evaluated{request, context, execution_trace}: L.ex_false({U.view(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Evaluated{request, context, execution_trace}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case True{} Q.Operated{schema, state, operation, result}: L.ex_false({U.view(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Operated{schema, state, operation, result}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case True{} Q.Prepared{response, bytes}: L.ex_false({U.view(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Prepared{response, bytes}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case True{} Q.Published{state}: L.ex_false({U.view(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Published{state}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case True{} Q.Visible{state}: L.ex_false({U.view(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Visible{state}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case True{} Q.Failed{stage, identifier, fatal}: L.ex_false({U.view(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Failed{stage, identifier, fatal}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case True{} Q.Completed{response, state, closes}: L.ex_false({U.view(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Completed{response, state, closes}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case True{} Q.Delivered{bytes}: L.ex_false({U.view(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Delivered{bytes}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case True{} Q.Interrupted{prefix}: L.ex_false({U.view(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Interrupted{prefix}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case True{} Q.Closed{}: L.ex_false({U.view(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Closed{}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case True{} Q.Next{previous, initial}: L.ex_false({U.view(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Next{previous, initial}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case True{} Q.Inspection{description}: L.ex_false({U.view(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Inspection{description}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))
    case True{} Q.Effect{description}: L.ex_false({U.view(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Effect{description}))) == U.VoidView{} : U.View}, F.false_negative_true(inside))


# Every nonzero tag is excluded: kind0 yields NoTag1(selection), kind1
# NoTag2(mutation), kind2 NoTag3(conclusion), kind3 NoTag4(publication).
def internal_frames_exclude_nonzero_tags(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +frames: List<&2, Q.Frame>, +world: Nat, +input: X.Reception, +selected: D.State, +mode: Bool, +code: String, +kind: Nat,
  actual: Micro.Internal(frames)) -> U.NoTag(Succ{kind}, U.values(c, binding, public, Engine.stamp(world, input, selected, C.core(mode, code, frames)))):
  match frames actual:
    case Nil{} _: Unit{}
    case Con{+frame, +rest} L.Both{first, later}:
      L.Both{Equal.cong(U.View, Bool, value => Nat.is_eq(U.tag(value), Succ{kind}),
        U.view(E.core_fact(mode, Q.fact_of_frame(c, Source.program(binding, Host.origin(public, code)), frame))), U.VoidView{},
        internal_frame_has_no_service_view(c, Source.program(binding, Host.origin(public, code)), mode, frame, first)),
        internal_frames_exclude_nonzero_tags(c, binding, public, rest, world, input, selected, mode, code, kind, later)}


law every_actual_decode_prelude_excludes_selection_mutation_conclusion_and_publication:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +current: D.State
  for +input: X.Reception
  for +world: Nat
  for +selected: D.State
  for +mode: Bool
  for +code: String
  for +kind: Nat
  U.NoTag(Succ{kind}, U.values(c, binding, public,
    Engine.stamp(world, input, selected, C.core(mode, code, Decode.frames(Decode.run(c, current, input))))))
def every_actual_decode_prelude_excludes_selection_mutation_conclusion_and_publication(c, binding, public, current, input, world, selected, mode, code, kind):
  internal_frames_exclude_nonzero_tags(c, binding, public, Decode.frames(Decode.run(c, current, input)), world, input, selected, mode, code, kind,
    every_actual_decode_prelude_contains_only_internal_frames(c, current, input))
