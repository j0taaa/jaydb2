# Finite actual execution generation exposes its own final evaluation query.
# The witness retains the exact bound/canonical source origin and real ordinal;
# no caller-supplied completed trace or virtual observer is introduced.
import Base
import ../../../../contract/Data.bend as D
import ../../../../contract/Interface.bend as I
import ../../../../contract/Logic.bend as L
import ../../../../contract/Protocol.bend as P
import ../../../../contract/Requirements.bend as R
import ../../../../contract/Semantics.bend as S
import ../../../../src/Core.bend as Core
import ../../../ExecutionService.bend as Adapter
import ../../../Foundations.bend as F
import ../../../HostTransitions.bend as Host
import ../../../ProtocolService.bend as Q
import ../../../SourceService.bend as Source
import ../EventObserver.bend as O
import ../FrameBounds.bend as B
import ../TimeEmbedding.bend as Time
import ./AuditQueries.bend as Queries
import ./Common.bend as C
import ./PublicationFinalized.bend as Final


type Framing is Data:
  Canonical{code: String}
  Bound{origin: Source.JudgmentSyntactic}


def frame(kind: Framing, mode: Bool, frame: Q.Frame) -> O.AuditEvent:
  match kind:
    case Canonical{code}: O.Core{mode, code, frame}
    case Bound{origin}: O.BoundCore{mode, origin, frame}


def frames(kind: Framing, mode: Bool, frames: List<&2, Q.Frame>) -> List<&2, O.AuditEvent>:
  match kind:
    case Canonical{code}: C.core(mode, code, frames)
    case Bound{origin}: C.bound_core(mode, origin, frames)


def Present(~c: S.Configuration, +kind: Framing, +mode: Bool, +request: P.Request, +context: D.Context, +source: List<&2, O.AuditEvent>, -at: Nat, +response: S.Response, +state: D.State) -> Type:
  &index: Nat -> &events: List<&2, S.OperationEvent> -> &proposal: S.Response ->
    L.E<{Nat.is_lt(index, at) == True{} : Bool},
      L.E<{B.query(O.AuditEvent, source, index) == Some{frame(kind, mode, Q.Evaluated{request, context, S.Final{state, events, proposal}})} : Maybe<&2, O.AuditEvent>},
        {R.finalize(proposal, c, state) == response : S.Response}>>


def lift(~c: S.Configuration, +kind: Framing, +mode: Bool, +request: P.Request, +context: D.Context,
  +prefix: List<&2, O.AuditEvent>, +suffix: List<&2, O.AuditEvent>, +at: Nat, +response: S.Response, +state: D.State,
  actual: Present(c, kind, mode, request, context, suffix, at, response, state)) -> Present(c, kind, mode, request, context, C.append(prefix, suffix), Nat.add(B.count(O.AuditEvent, prefix), at), response, state):
  match actual:
    case (+index, +events, +proposal, L.Both{order, L.Both{query, finalized}}):
      (Nat.add(B.count(O.AuditEvent, prefix), index), events, proposal, L.Both{Time.adding_prefix_preserves_strict_order(B.count(O.AuditEvent, prefix), index, at, order),
        L.Both{Queries.suffix_query(prefix, suffix, index, frame(kind, mode, Q.Evaluated{request, context, S.Final{state, events, proposal}}), query), finalized}})


def query_core(+mode: Bool, +code: String, source: List<&2, Q.Frame>, index: Nat, +target: Q.Frame,
  found: {Q.query(source, index) == Some{target} : Maybe<&2, Q.Frame>}) -> {B.query(O.AuditEvent, C.core(mode, code, source), index) == Some{O.Core{mode, code, target}} : Maybe<&2, O.AuditEvent>}:
  match source index:
    case Nil{} _: L.ex_false({B.query(O.AuditEvent, Nil{}, index) == Some{O.Core{mode, code, target}} : Maybe<&2, O.AuditEvent>}, F.none_negative_some(Q.Frame, target, found))
    case Con{+head, rest} 0n: Equal.cong(Q.Frame, Maybe<&2, O.AuditEvent>, value => Some{O.Core{mode, code, value}}, head, target, F.some_injective(Q.Frame, head, target, found))
    case Con{head, rest} 1n+k: query_core(mode, code, rest, k, target, found)


def query_bound(+mode: Bool, +origin: Source.JudgmentSyntactic, source: List<&2, Q.Frame>, index: Nat, +target: Q.Frame,
  found: {Q.query(source, index) == Some{target} : Maybe<&2, Q.Frame>}) -> {B.query(O.AuditEvent, C.bound_core(mode, origin, source), index) == Some{O.BoundCore{mode, origin, target}} : Maybe<&2, O.AuditEvent>}:
  match source index:
    case Nil{} _: L.ex_false({B.query(O.AuditEvent, Nil{}, index) == Some{O.BoundCore{mode, origin, target}} : Maybe<&2, O.AuditEvent>}, F.none_negative_some(Q.Frame, target, found))
    case Con{+head, rest} 0n: Equal.cong(Q.Frame, Maybe<&2, O.AuditEvent>, value => Some{O.BoundCore{mode, origin, value}}, head, target, F.some_injective(Q.Frame, head, target, found))
    case Con{head, rest} 1n+k: query_bound(mode, origin, rest, k, target, found)


def query_frame(+kind: Framing, +mode: Bool, source: List<&2, Q.Frame>, index: Nat, +target: Q.Frame,
  found: {Q.query(source, index) == Some{target} : Maybe<&2, Q.Frame>}) -> {B.query(O.AuditEvent, frames(kind, mode, source), index) == Some{frame(kind, mode, target)} : Maybe<&2, O.AuditEvent>}:
  match kind:
    case Canonical{+code}:
      query_core(mode, code, source, index, target, found)
    case Bound{+origin}:
      query_bound(mode, origin, source, index, target, found)


def origin(public: List<&2, Source.FileSource>, kind: Framing) -> Source.JudgmentSyntactic:
  match kind:
    case Canonical{code}: Host.origin(public, code)
    case Bound{origin}: origin


def header(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +kind: Framing, +mode: Bool, +request: P.Request, +context: D.Context, +before: D.State, +steps: Nat) -> List<&2, O.AuditEvent>:
  frames(kind, mode, Con{Q.Started{request, context}, Q.expand_exec(request, context,
    Adapter.generate(steps, Core.start(Source.program(binding, origin(public, kind)), context, I.arguments(request), before), S.schema(c)))})


def header_query(+kind: Framing, +mode: Bool, +request: P.Request, +context: D.Context, +source: List<&2, Q.FrameExec>, +index: Nat, +target: S.Trace,
  found: {Adapter.query(source, index) == Some{Q.Evaluation{target}} : Maybe<&2, Q.FrameExec>}) ->
  {B.query(O.AuditEvent, frames(kind, mode, Con{Q.Started{request, context}, Q.expand_exec(request, context, source)}), Succ{index}) == Some{frame(kind, mode, Q.Evaluated{request, context, target})} : Maybe<&2, O.AuditEvent>}:
  query_frame(kind, mode, Con{Q.Started{request, context}, Q.expand_exec(request, context, source)}, Succ{index}, Q.Evaluated{request, context, target},
    Adapter.expand_preserves_query(request, context, source, index, Q.Evaluation{target}, found))


def located_final(~c: S.Configuration, +kind: Framing, +mode: Bool, +request: P.Request, +context: D.Context, +prefix: List<&2, O.AuditEvent>, +later: List<&2, O.AuditEvent>, +tail_index: Nat, +response: S.Response, +state: D.State,
  +events: List<&2, S.OperationEvent>, +proposal: S.Response, +index: Nat,
  queries: L.E<{B.query(O.AuditEvent, prefix, index) == Some{frame(kind, mode, Q.Evaluated{request, context, S.Final{state, events, proposal}})} : Maybe<&2, O.AuditEvent>},
    {B.query(O.AuditEvent, prefix, index) == Some{frame(kind, mode, Q.Evaluated{request, context, S.Final{state, events, proposal}})} : Maybe<&2, O.AuditEvent>}>,
  finalized: {R.finalize(proposal, c, state) == response : S.Response}) -> Present(c, kind, mode, request, context, C.append(prefix, later), Nat.add(B.count(O.AuditEvent, prefix), tail_index), response, state):
  match queries:
    case L.Both{at_order, retained}:
      (index, events, proposal, L.Both{Time.strict_right_extension(index, B.count(O.AuditEvent, prefix), tail_index,
        B.successful_query_is_strictly_inside_actual_list(O.AuditEvent, prefix, index, frame(kind, mode, Q.Evaluated{request, context, S.Final{state, events, proposal}}), at_order)),
        L.Both{Queries.prefix_query(prefix, later, index, frame(kind, mode, Q.Evaluated{request, context, S.Final{state, events, proposal}}), retained), finalized}})


def final_index(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +kind: Framing, +mode: Bool, +request: P.Request, +context: D.Context, +before: D.State, +steps: Nat,
  +later: List<&2, O.AuditEvent>, +tail_index: Nat, +response: S.Response, +state: D.State, +events: List<&2, S.OperationEvent>, +proposal: S.Response,
  finalized: {R.finalize(proposal, c, state) == response : S.Response},
  indexed: &index: Nat -> {Adapter.query(Adapter.generate(steps, Core.start(Source.program(binding, origin(public, kind)), context, I.arguments(request), before), S.schema(c)), index) == Some{Q.Evaluation{S.Final{state, events, proposal}}} : Maybe<&2, Q.FrameExec>}) ->
  Present(c, kind, mode, request, context, C.append(header(c, binding, public, kind, mode, request, context, before, steps), later), Nat.add(B.count(O.AuditEvent, header(c, binding, public, kind, mode, request, context, before, steps)), tail_index), response, state):
  match indexed:
    case (+index, query):
      located_final(c, kind, mode, request, context, header(c, binding, public, kind, mode, request, context, before, steps), later, tail_index, response, state, events, proposal, Succ{index},
        Q.equality_reopenable(Maybe<&2, O.AuditEvent>, B.query(O.AuditEvent, header(c, binding, public, kind, mode, request, context, before, steps), Succ{index}), Some{frame(kind, mode, Q.Evaluated{request, context, S.Final{state, events, proposal}})},
          header_query(kind, mode, request, context, Adapter.generate(steps, Core.start(Source.program(binding, origin(public, kind)), context, I.arguments(request), before), S.schema(c)), index, S.Final{state, events, proposal}, query)), finalized)


law the_actual_generated_header_exposes_its_exact_final_evaluation_strictly_before_every_later_result_event:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +kind: Framing
  for +mode: Bool
  for +request: P.Request
  for +context: D.Context
  for +before: D.State
  for +steps: Nat
  for +later: List<&2, O.AuditEvent>
  for +tail_index: Nat
  for +response: S.Response
  for +state: D.State
  for actual: Final.Finalized(c, Core.traverse(steps, Core.start(Source.program(binding, origin(public, kind)), context, I.arguments(request), before), S.schema(c)), response, state)
  Present(c, kind, mode, request, context, C.append(header(c, binding, public, kind, mode, request, context, before, steps), later), Nat.add(B.count(O.AuditEvent, header(c, binding, public, kind, mode, request, context, before, steps)), tail_index), response, state)
def the_actual_generated_header_exposes_its_exact_final_evaluation_strictly_before_every_later_result_event(c, binding, public, kind, mode, request, context, before, steps, later, tail_index, response, state, actual):
  match actual:
    case (+events, +proposal, L.Both{traced, finalized}):
      final_index(c, binding, public, kind, mode, request, context, before, steps, later, tail_index, response, state, events, proposal, finalized,
        Adapter.last_present_has_index(Adapter.generate(steps, Core.start(Source.program(binding, origin(public, kind)), context, I.arguments(request), before), S.schema(c)), Q.Evaluation{S.Final{state, events, proposal}},
          Equal.trans(Maybe<&2, Q.FrameExec>, Adapter.last(Adapter.generate(steps, Core.start(Source.program(binding, origin(public, kind)), context, I.arguments(request), before), S.schema(c))),
            Some{Q.Evaluation{Core.traverse(steps, Core.start(Source.program(binding, origin(public, kind)), context, I.arguments(request), before), S.schema(c))}}, Some{Q.Evaluation{S.Final{state, events, proposal}}},
            Adapter.last_represents_all_execution_trace(steps, Core.start(Source.program(binding, origin(public, kind)), context, I.arguments(request), before), S.schema(c)),
            Equal.cong(S.Trace, Maybe<&2, Q.FrameExec>, value => Some{Q.Evaluation{value}}, Core.traverse(steps, Core.start(Source.program(binding, origin(public, kind)), context, I.arguments(request), before), S.schema(c)), S.Final{state, events, proposal}, traced))))
