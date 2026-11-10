# Exact success/refusal/error rendering, including post-store fatal failure.
# No publication is assumed; publication is inspected from its real renderer.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Resources.bend as X
import ../../../../../contract/Semantics.bend as S
import ../../../../../src/Core.bend as Core
import ../../../../ProtocolService.bend as Q
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/PreparePhases.bend as V
import ../../../model/EventObserver.bend as O
import ../../../model/serial/Common.bend as C
import ../../../model/serial/ExecutionPhases.bend as Exec
import ./Meaning.bend as M
import ./Algebra.bend as A
import ./RuntimeBase.bend as R

def publication_quiet(+mode: Bool, +before: E.Snapshot, +after: E.Snapshot, response: S.Response, +bytes: List<&2, U32>) ->
  {M.quiet(Exec.publication(mode, before, after, response, bytes)) == True{} : Bool}:
  match response:
    case S.Response{S.Success{}, value}: {==}
    case S.Response{S.Refusal{}, value}: {==}
    case S.Response{S.Input{}, value}: {==}
    case S.Response{S.Authentication{}, value}: {==}
    case S.Response{S.Certificate{}, value}: {==}
    case S.Response{S.DataError{}, value}: {==}
    case S.Response{S.Limit{}, value}: {==}
    case S.Response{S.Failure{}, value}: {==}

def middle_layout(+prepared: O.AuditEvent, +middle: List<&2, O.AuditEvent>, +concluded: O.AuditEvent, +tail: List<&2, O.AuditEvent>) ->
  {C.append(C.append([prepared], C.append(middle, [concluded])), tail) == C.append(Con{prepared, middle}, Con{concluded, tail}) : List<&2, O.AuditEvent>}:
  Equal.cong(List<&2, O.AuditEvent>, List<&2, O.AuditEvent>, rest => Con{prepared, rest}, C.append(C.append(middle, [concluded]), tail), C.append(middle, Con{concluded, tail}), A.append_assoc(middle, [concluded], tail))

def concluded_layout(+mode: Bool, +code: String, +before: E.Snapshot, +state: D.State, +response: S.Response, +bytes: List<&2, U32>, +send: V.SendReturn) ->
  {C.events(Exec.concluded(mode, code, before, Core.Conclusion{state, response, bytes}, send)) ==
    C.append(Con{O.Core{mode, code, Q.Prepared{response, bytes}}, Exec.publication(mode, before, Exec.published(before, Core.Conclusion{state, response, bytes}), response, bytes)},
      Con{O.Core{mode, code, Q.Completed{response, E.database(Exec.published(before, Core.Conclusion{state, response, bytes})), False{}}},
        C.events(C.delivery(mode, code, Exec.published(before, Core.Conclusion{state, response, bytes}), E.Transaction{response}, bytes, False{}, send))}) : List<&2, O.AuditEvent>}:
  Equal.trans(List<&2, O.AuditEvent>, C.events(Exec.concluded(mode, code, before, Core.Conclusion{state, response, bytes}, send)),
    C.append(C.append([O.Core{mode, code, Q.Prepared{response, bytes}}], C.append(Exec.publication(mode, before, Exec.published(before, Core.Conclusion{state, response, bytes}), response, bytes),
      [O.Core{mode, code, Q.Completed{response, E.database(Exec.published(before, Core.Conclusion{state, response, bytes})), False{}}}])),
      C.events(C.delivery(mode, code, Exec.published(before, Core.Conclusion{state, response, bytes}), E.Transaction{response}, bytes, False{}, send))),
    C.append(Con{O.Core{mode, code, Q.Prepared{response, bytes}}, Exec.publication(mode, before, Exec.published(before, Core.Conclusion{state, response, bytes}), response, bytes)},
      Con{O.Core{mode, code, Q.Completed{response, E.database(Exec.published(before, Core.Conclusion{state, response, bytes})), False{}}},
        C.events(C.delivery(mode, code, Exec.published(before, Core.Conclusion{state, response, bytes}), E.Transaction{response}, bytes, False{}, send))}),
    A.prefix_events(C.append([O.Core{mode, code, Q.Prepared{response, bytes}}], C.append(Exec.publication(mode, before, Exec.published(before, Core.Conclusion{state, response, bytes}), response, bytes),
      [O.Core{mode, code, Q.Completed{response, E.database(Exec.published(before, Core.Conclusion{state, response, bytes})), False{}}}])),
      C.delivery(mode, code, Exec.published(before, Core.Conclusion{state, response, bytes}), E.Transaction{response}, bytes, False{}, send)),
    middle_layout(O.Core{mode, code, Q.Prepared{response, bytes}}, Exec.publication(mode, before, Exec.published(before, Core.Conclusion{state, response, bytes}), response, bytes),
      O.Core{mode, code, Q.Completed{response, E.database(Exec.published(before, Core.Conclusion{state, response, bytes})), False{}}},
      C.events(C.delivery(mode, code, Exec.published(before, Core.Conclusion{state, response, bytes}), E.Transaction{response}, bytes, False{}, send))))

def prepared_concluded(+code: String, +before: E.Snapshot, +state: D.State, +response: S.Response, +bytes: List<&2, U32>, +send: V.SendReturn) ->
  M.Shape<C.events(Exec.concluded(True{}, code, before, Core.Conclusion{state, response, bytes}, send))>:
  %Equal.sym(List<&2, O.AuditEvent>, C.events(Exec.concluded(True{}, code, before, Core.Conclusion{state, response, bytes}, send)),
    C.append(Con{O.Core{True{}, code, Q.Prepared{response, bytes}}, Exec.publication(True{}, before, Exec.published(before, Core.Conclusion{state, response, bytes}), response, bytes)},
      Con{O.Core{True{}, code, Q.Completed{response, E.database(Exec.published(before, Core.Conclusion{state, response, bytes})), False{}}},
        C.events(C.delivery(True{}, code, Exec.published(before, Core.Conclusion{state, response, bytes}), E.Transaction{response}, bytes, False{}, send))}),
    concluded_layout(True{}, code, before, state, response, bytes, send)) : M.Shape<_>
  M.TransactionShape{Con{O.Core{True{}, code, Q.Prepared{response, bytes}}, Exec.publication(True{}, before, Exec.published(before, Core.Conclusion{state, response, bytes}), response, bytes)},
    C.events(C.delivery(True{}, code, Exec.published(before, Core.Conclusion{state, response, bytes}), E.Transaction{response}, bytes, False{}, send)),
    O.Core{True{}, code, Q.Completed{response, E.database(Exec.published(before, Core.Conclusion{state, response, bytes})), False{}}},
    response, E.database(Exec.published(before, Core.Conclusion{state, response, bytes})), bytes, 0n, O.Core{True{}, code, Q.Prepared{response, bytes}},
    {==}, {==}, A.quiet_cons(O.Core{True{}, code, Q.Prepared{response, bytes}}, Exec.publication(True{}, before, Exec.published(before, Core.Conclusion{state, response, bytes}), response, bytes), {==},
      publication_quiet(True{}, before, Exec.published(before, Core.Conclusion{state, response, bytes}), response, bytes)),
    R.quiet_delivery(True{}, code, Exec.published(before, Core.Conclusion{state, response, bytes}), E.Transaction{response}, bytes, False{}, send), {==}, {==}}

def ordinary_concluded(+code: String, +before: E.Snapshot, +state: D.State, +response: S.Response, +bytes: List<&2, U32>, +send: V.SendReturn) ->
  {M.quiet(C.events(Exec.concluded(False{}, code, before, Core.Conclusion{state, response, bytes}, send))) == True{} : Bool}:
  %Equal.sym(List<&2, O.AuditEvent>, C.events(Exec.concluded(False{}, code, before, Core.Conclusion{state, response, bytes}, send)),
    C.append(Con{O.Core{False{}, code, Q.Prepared{response, bytes}}, Exec.publication(False{}, before, Exec.published(before, Core.Conclusion{state, response, bytes}), response, bytes)},
      Con{O.Core{False{}, code, Q.Completed{response, E.database(Exec.published(before, Core.Conclusion{state, response, bytes})), False{}}},
        C.events(C.delivery(False{}, code, Exec.published(before, Core.Conclusion{state, response, bytes}), E.Transaction{response}, bytes, False{}, send))}),
    concluded_layout(False{}, code, before, state, response, bytes, send)) : {M.quiet(_) == True{} : Bool}
  A.quiet_append(Con{O.Core{False{}, code, Q.Prepared{response, bytes}}, Exec.publication(False{}, before, Exec.published(before, Core.Conclusion{state, response, bytes}), response, bytes)},
    Con{O.Core{False{}, code, Q.Completed{response, E.database(Exec.published(before, Core.Conclusion{state, response, bytes})), False{}}},
      C.events(C.delivery(False{}, code, Exec.published(before, Core.Conclusion{state, response, bytes}), E.Transaction{response}, bytes, False{}, send))},
    A.quiet_cons(O.Core{False{}, code, Q.Prepared{response, bytes}}, Exec.publication(False{}, before, Exec.published(before, Core.Conclusion{state, response, bytes}), response, bytes), {==},
      publication_quiet(False{}, before, Exec.published(before, Core.Conclusion{state, response, bytes}), response, bytes)),
    A.quiet_cons(O.Core{False{}, code, Q.Completed{response, E.database(Exec.published(before, Core.Conclusion{state, response, bytes})), False{}}},
      C.events(C.delivery(False{}, code, Exec.published(before, Core.Conclusion{state, response, bytes}), E.Transaction{response}, bytes, False{}, send)), {==},
      R.quiet_delivery(False{}, code, Exec.published(before, Core.Conclusion{state, response, bytes}), E.Transaction{response}, bytes, False{}, send)))

def concluded_returns(mode: Bool, +code: String, +before: E.Snapshot, +state: D.State, +response: S.Response, +bytes: List<&2, U32>, +send: V.SendReturn) ->
  M.Shape<C.events(Exec.concluded(mode, code, before, Core.Conclusion{state, response, bytes}, send))>:
  match mode:
    case False{}: M.Quiet{ordinary_concluded(code, before, state, response, bytes, send)}
    case True{}: prepared_concluded(code, before, state, response, bytes, send)

def concluded(+mode: Bool, +code: String, +before: E.Snapshot, conclusion: Core.Conclusion, +send: V.SendReturn) ->
  M.Shape<C.events(Exec.concluded(mode, code, before, conclusion, send))>:
  match conclusion:
    case Core.Conclusion{state, response, bytes}: concluded_returns(mode, code, before, state, response, bytes, send)

def fatal_after_store(+mode: Bool, +code: String, +before: E.Snapshot, conclusion: Core.Conclusion, +stage: X.Stage, +identifier: String) ->
  M.Shape<C.events(Exec.fatal_after_store(mode, code, before, conclusion, stage, identifier))>:
  match conclusion:
    case Core.Conclusion{+state, +response, +bytes}:
      M.Quiet{A.quiet_cons(O.Core{mode, code, Q.Prepared{response, bytes}},
        C.append(Exec.publication(mode, before, Exec.published(before, Core.Conclusion{state, response, bytes}), response, bytes), C.core(mode, code, [Q.Failed{stage, identifier, True{}}, Q.Closed{}])), {==},
        A.quiet_append(Exec.publication(mode, before, Exec.published(before, Core.Conclusion{state, response, bytes}), response, bytes), C.core(mode, code, [Q.Failed{stage, identifier, True{}}, Q.Closed{}]),
          publication_quiet(mode, before, Exec.published(before, Core.Conclusion{state, response, bytes}), response, bytes), {==}))}
