# Complete ordinary/cached Core-prefix replay. Success changes the exact paired
# DB/response once; refusal/errors do not. A fatal post-store return retains the
# real publication, and pending preparation has no fabricated conclusion.
import Base
import ../../../../contract/Data.bend as D
import ../../../../contract/Interface.bend as I
import ../../../../contract/Logic.bend as L
import ../../../../contract/Protocol.bend as P
import ../../../../contract/Resources.bend as X
import ../../../../contract/Semantics.bend as S
import ../../../../src/Core.bend as Core
import ../../../ExecutionService.bend as Execute
import ../../../HostTransitions.bend as Host
import ../../../ProtocolService.bend as Q
import ../../../RoutesService.bend as Route
import ../../../SourceService.bend as Source
import ../../specification/ServiceLaws.bend as E
import ../../phases/PreparePhases.bend as V
import ../EventObserver.bend as O
import ./Common.bend as C
import ./CommonHistory.bend as Common
import ./ExecutionPhases.bend as Execution
import ./LocalHistory.bend as J


def published_prefix(+position: J.Position, +mode: Bool, +code: String, +before: E.Snapshot, +after: E.Snapshot,
  +response: S.Response, +bytes: List<&2, U32>,
  scope: {E.instance(before) == E.instance(after) : String}, selection: {J.selected(position) == E.database(before) : D.State}) ->
  J.Sound(position, [O.Core{mode, code, Q.Prepared{response, bytes}}, O.Publication{mode, response, bytes, before, after}, O.Core{mode, code, Q.Completed{response, E.database(after), False{}}}], before, after):
  J.quiet_push(position, O.Core{mode, code, Q.Prepared{response, bytes}},
    [O.Publication{mode, response, bytes, before, after}, O.Core{mode, code, Q.Completed{response, E.database(after), False{}}}], before, after, {==},
    J.mutation_push(position, O.Publication{mode, response, bytes, before, after}, [O.Core{mode, code, Q.Completed{response, E.database(after), False{}}}], mode, E.Publish{response, bytes}, before, after, after,
      {==}, scope, selection, J.quiet_all(position, [O.Core{mode, code, Q.Completed{response, E.database(after), False{}}}], after, L.Both{{==}, Unit{}})))


def success_concluded(+position: J.Position, +mode: Bool, +code: String, +before: E.Snapshot, +state: D.State, +value: D.Value,
  +bytes: List<&2, U32>, +send: V.SendReturn, selection: {J.selected(position) == E.database(before) : D.State}) ->
  J.CallSound(position, Execution.concluded(mode, code, before, Core.Conclusion{state, S.Response{S.Success{}, value}, bytes}, send), before):
  +response: S.Response = S.Response{S.Success{}, value}
  +after: E.Snapshot = E.Snapshot{E.instance(before), state, bytes, E.registry(before)}
  J.full_prefix_call(position, [O.Core{mode, code, Q.Prepared{response, bytes}}, O.Publication{mode, response, bytes, before, after}, O.Core{mode, code, Q.Completed{response, E.database(after), False{}}}],
    C.delivery(mode, code, after, E.Transaction{response}, bytes, False{}, send), before, after,
    published_prefix(position, mode, code, before, after, response, bytes, {==}, selection), Common.delivery(position, mode, code, after, E.Transaction{response}, bytes, False{}, send))


def unchanged_concluded(+position: J.Position, +mode: Bool, +code: String, +before: E.Snapshot, +response: S.Response, +bytes: List<&2, U32>, +send: V.SendReturn) ->
  J.CallSound(position, C.prefix([O.Core{mode, code, Q.Prepared{response, bytes}}, O.Core{mode, code, Q.Completed{response, E.database(before), False{}}}],
    C.delivery(mode, code, before, E.Transaction{response}, bytes, False{}, send)), before):
  J.prefix_call(position, [O.Core{mode, code, Q.Prepared{response, bytes}}, O.Core{mode, code, Q.Completed{response, E.database(before), False{}}}],
    C.delivery(mode, code, before, E.Transaction{response}, bytes, False{}, send), before,
    L.Both{{==}, L.Both{{==}, Unit{}}}, Common.delivery(position, mode, code, before, E.Transaction{response}, bytes, False{}, send))


def concluded(+position: J.Position, +mode: Bool, +code: String, +before: E.Snapshot, +conclusion: Core.Conclusion, +send: V.SendReturn,
  selection: {J.selected(position) == E.database(before) : D.State}) -> J.CallSound(position, Execution.concluded(mode, code, before, conclusion, send), before):
  match conclusion:
    case Core.Conclusion{state, S.Response{status, value}, bytes}:
      match status:
        case S.Success{}: success_concluded(position, mode, code, before, state, value, bytes, send, selection)
        case S.Input{}: unchanged_concluded(position, mode, code, before, S.Response{S.Input{}, value}, bytes, send)
        case S.Authentication{}: unchanged_concluded(position, mode, code, before, S.Response{S.Authentication{}, value}, bytes, send)
        case S.Certificate{}: unchanged_concluded(position, mode, code, before, S.Response{S.Certificate{}, value}, bytes, send)
        case S.DataError{}: unchanged_concluded(position, mode, code, before, S.Response{S.DataError{}, value}, bytes, send)
        case S.Limit{}: unchanged_concluded(position, mode, code, before, S.Response{S.Limit{}, value}, bytes, send)
        case S.Failure{}: unchanged_concluded(position, mode, code, before, S.Response{S.Failure{}, value}, bytes, send)
        case S.Refusal{}: unchanged_concluded(position, mode, code, before, S.Response{S.Refusal{}, value}, bytes, send)


def success_fatal(+position: J.Position, +mode: Bool, +code: String, +before: E.Snapshot, +state: D.State, +value: D.Value,
  +bytes: List<&2, U32>, +stage: X.Stage, +id: String,
  selection: {J.selected(position) == E.database(before) : D.State}) ->
  J.CallSound(position, Execution.fatal_after_store(mode, code, before, Core.Conclusion{state, S.Response{S.Success{}, value}, bytes}, stage, id), before):
  +response: S.Response = S.Response{S.Success{}, value}
  +after: E.Snapshot = E.Snapshot{E.instance(before), state, bytes, E.registry(before)}
  J.quiet_push(position, O.Core{mode, code, Q.Prepared{response, bytes}},
    [O.Publication{mode, response, bytes, before, after}, O.Core{mode, code, Q.Failed{stage, id, True{}}}, O.Core{mode, code, Q.Closed{}}], before, after, {==},
    J.mutation_push(position, O.Publication{mode, response, bytes, before, after}, [O.Core{mode, code, Q.Failed{stage, id, True{}}}, O.Core{mode, code, Q.Closed{}}], mode, E.Publish{response, bytes}, before, after, after,
      {==}, {==}, selection, J.quiet_all(position, C.core(mode, code, [Q.Failed{stage, id, True{}}, Q.Closed{}]), after, J.core_quiet(mode, code, [Q.Failed{stage, id, True{}}, Q.Closed{}]))))


def unchanged_fatal(+position: J.Position, +mode: Bool, +code: String, +before: E.Snapshot, +response: S.Response, +bytes: List<&2, U32>, +stage: X.Stage, +id: String) ->
  J.Sound(position, C.core(mode, code, [Q.Prepared{response, bytes}, Q.Failed{stage, id, True{}}, Q.Closed{}]), before, before):
  J.quiet_all(position, C.core(mode, code, [Q.Prepared{response, bytes}, Q.Failed{stage, id, True{}}, Q.Closed{}]), before, J.core_quiet(mode, code, [Q.Prepared{response, bytes}, Q.Failed{stage, id, True{}}, Q.Closed{}]))


def fatal_after_store(+position: J.Position, +mode: Bool, +code: String, +before: E.Snapshot, +conclusion: Core.Conclusion, +stage: X.Stage, +id: String,
  selection: {J.selected(position) == E.database(before) : D.State}) -> J.CallSound(position, Execution.fatal_after_store(mode, code, before, conclusion, stage, id), before):
  match conclusion:
    case Core.Conclusion{state, S.Response{status, value}, bytes}:
      match status:
        case S.Success{}: success_fatal(position, mode, code, before, state, value, bytes, stage, id, selection)
        case S.Input{}: unchanged_fatal(position, mode, code, before, S.Response{S.Input{}, value}, bytes, stage, id)
        case S.Authentication{}: unchanged_fatal(position, mode, code, before, S.Response{S.Authentication{}, value}, bytes, stage, id)
        case S.Certificate{}: unchanged_fatal(position, mode, code, before, S.Response{S.Certificate{}, value}, bytes, stage, id)
        case S.DataError{}: unchanged_fatal(position, mode, code, before, S.Response{S.DataError{}, value}, bytes, stage, id)
        case S.Limit{}: unchanged_fatal(position, mode, code, before, S.Response{S.Limit{}, value}, bytes, stage, id)
        case S.Failure{}: unchanged_fatal(position, mode, code, before, S.Response{S.Failure{}, value}, bytes, stage, id)
        case S.Refusal{}: unchanged_fatal(position, mode, code, before, S.Response{S.Refusal{}, value}, bytes, stage, id)


def cleanup_history(+position: J.Position, +mode: Bool, +code: String, +before: E.Snapshot, +prepared: Core.Prepared, +cleanup: Route.Cleanup, +send: V.SendReturn,
  selection: {J.selected(position) == E.database(before) : D.State}) -> J.CallSound(position, Execution.cleanup(mode, code, before, prepared, cleanup, send), before):
  match cleanup:
    case Route.Clears{}: concluded(position, mode, code, before, Core.conclude(prepared, E.database(before)), send, selection)
    case Route.FatalAfterStore{stage, id}: fatal_after_store(position, mode, code, before, Core.conclude(prepared, E.database(before)), stage, id, selection)
    case Route.PendingCleanup{}:
      J.prefix_call(position, C.core(mode, code, [Route.frame_prepared(prepared)]), C.pending(before), before, J.core_quiet(mode, code, [Route.frame_prepared(prepared)]), J.no_events(position, before))
    case Route.ErrorCleanup{id, fatal}:
      J.prefix_call(position, C.core(mode, code, [Route.frame_prepared(prepared)]), C.failed(mode, code, before, X.Prepare{}, id, fatal, send), before,
        J.core_quiet(mode, code, [Route.frame_prepared(prepared)]), Common.failed(position, mode, code, before, X.Prepare{}, id, fatal, send))


def prepared_result(+position: J.Position, +mode: Bool, +code: String, +before: E.Snapshot, +prepared: Maybe<&2, Core.Prepared>, +cleanup: Route.Cleanup, +send: V.SendReturn,
  selection: {J.selected(position) == E.database(before) : D.State}) -> J.CallSound(position, Execution.prepared_result(mode, code, before, prepared, cleanup, send), before):
  match prepared:
    case None{}: J.no_events(position, before)
    case Some{prepared}: cleanup_history(position, mode, code, before, prepared, cleanup, send, selection)


def trace_result(~c: S.Configuration, +position: J.Position, +mode: Bool, +code: String, +before: E.Snapshot,
  +end: Execution.End, +trace: S.Trace, +send: V.SendReturn,
  selection: {J.selected(position) == E.database(before) : D.State}) -> J.CallSound(position, Execution.trace_result(c, mode, code, before, end, trace, send), before):
  match end:
    case Execution.PrefixPending{}: J.no_events(position, before)
    case Execution.PrefixFailed{id, fatal}: Common.failed(position, mode, code, before, X.Execute{}, id, fatal, send)
    case Execution.FinishPrefix{cleanup}:
      match trace:
        case S.Prefix{working, events}: J.no_events(position, before)
        case S.Final{working, events, response}: prepared_result(position, mode, code, before, Core.prepare(Core.Stopped{working, events, response}, c), cleanup, send, selection)


def executed_bound_prefix(~c: S.Configuration, ~binding: Source.Source,
  +position: J.Position, +origin: Source.JudgmentSyntactic, +mode: Bool, +request: P.Request, +context: D.Context,
  +before: E.Snapshot, +steps: Nat, +end: Execution.End, +send: V.SendReturn,
  selection: {J.selected(position) == E.database(before) : D.State}) ->
  J.CallSound(position, Execution.executed_bound_prefix(c, binding, origin, mode, request, context, before, steps, end, send), before):
  J.prefix_call(position, C.bound_core(mode, origin, Con{Q.Started{request, context},
      Q.expand_exec(request, context, Execute.generate(steps, Core.start(Source.program(binding, origin), context, I.arguments(request), E.database(before)), S.schema(c)))}),
    Execution.trace_result(c, mode, I.code(request), before, end, Core.traverse(steps, Core.start(Source.program(binding, origin), context, I.arguments(request), E.database(before)), S.schema(c)), send), before,
    J.bound_core_quiet(mode, origin, Con{Q.Started{request, context}, Q.expand_exec(request, context, Execute.generate(steps, Core.start(Source.program(binding, origin), context, I.arguments(request), E.database(before)), S.schema(c)))}),
    trace_result(c, position, mode, I.code(request), before, end, Core.traverse(steps, Core.start(Source.program(binding, origin), context, I.arguments(request), E.database(before)), S.schema(c)), send, selection))


def run_bound(~c: S.Configuration, ~binding: Source.Source,
  +position: J.Position, +origin: Source.JudgmentSyntactic, +mode: Bool, +request: P.Request, +context: D.Context,
  +before: E.Snapshot, +execution: Execution.Request, +send: V.SendReturn,
  selection: {J.selected(position) == E.database(before) : D.State}) ->
  J.CallSound(position, Execution.run_bound(c, binding, origin, mode, request, context, before, execution, send), before):
  match execution:
    case Execution.StartPending{}: J.no_events(position, before)
    case Execution.StartFailed{id, fatal}: Common.failed(position, mode, I.code(request), before, X.Execute{}, id, fatal, send)
    case Execution.RunPrefix{steps, end}: executed_bound_prefix(c, binding, position, origin, mode, request, context, before, steps, end, send, selection)


def executed_prefix(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +position: J.Position, +mode: Bool, +request: P.Request, +context: D.Context,
  +before: E.Snapshot, +steps: Nat, +end: Execution.End, +send: V.SendReturn,
  selection: {J.selected(position) == E.database(before) : D.State}) ->
  J.CallSound(position, Execution.executed_prefix(c, binding, public, mode, request, context, before, steps, end, send), before):
  J.prefix_call(position, C.core(mode, I.code(request), Con{Q.Started{request, context},
      Q.expand_exec(request, context, Execute.generate(steps, Core.start(Source.program(binding, Host.origin(public, I.code(request))), context, I.arguments(request), E.database(before)), S.schema(c)))}),
    Execution.trace_result(c, mode, I.code(request), before, end, Core.traverse(steps, Core.start(Source.program(binding, Host.origin(public, I.code(request))), context, I.arguments(request), E.database(before)), S.schema(c)), send), before,
    J.core_quiet(mode, I.code(request), Con{Q.Started{request, context}, Q.expand_exec(request, context, Execute.generate(steps, Core.start(Source.program(binding, Host.origin(public, I.code(request))), context, I.arguments(request), E.database(before)), S.schema(c)))}),
    trace_result(c, position, mode, I.code(request), before, end, Core.traverse(steps, Core.start(Source.program(binding, Host.origin(public, I.code(request))), context, I.arguments(request), E.database(before)), S.schema(c)), send, selection))


def run(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +position: J.Position, +mode: Bool, +request: P.Request, +context: D.Context,
  +before: E.Snapshot, +execution: Execution.Request, +send: V.SendReturn,
  selection: {J.selected(position) == E.database(before) : D.State}) ->
  J.CallSound(position, Execution.run(c, binding, public, mode, request, context, before, execution, send), before):
  match execution:
    case Execution.StartPending{}: J.no_events(position, before)
    case Execution.StartFailed{id, fatal}: Common.failed(position, mode, I.code(request), before, X.Execute{}, id, fatal, send)
    case Execution.RunPrefix{steps, end}: executed_prefix(c, binding, public, position, mode, request, context, before, steps, end, send, selection)
