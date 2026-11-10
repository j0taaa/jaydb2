# Concrete DATA-only framing/dispatcher fixtures, not native IO witnesses.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/PreparedProtocol.bend as W
import ../../../contract/Protocol.bend as P
import ../../../contract/Resources.bend as X
import ../../../contract/Semantics.bend as S
import ../../../proof/service/specification/ServiceLaws.bend as E
import ../../../proof/service/phases/PreparePhases.bend as V
import ../../../proof/service/phases/InvalidationPhases.bend as N
import ../../../proof/service/model/serial/Dispatch.bend as Dispatch
import ../../../proof/service/model/serial/ExecutionPhases.bend as Execution
import ../../../proof/service/model/serial/Engine.bend as Engine


def configuration() -> S.Configuration:
  S.Configuration{D.Schema{[]}, S.NoneLaw{}, S.Limits{103n, 103n, 103n}, "fixture"}


def before() -> E.Snapshot:
  E.Snapshot{"fixture", D.State{[], []}, [], []}


def raw() -> P.Request:
  P.Request{"", "", D.VAbsent{}, ""}


def physical(valid: Bool, result: Maybe<&2, List<&2, U32>>) -> X.Reception:
  match result:
    case None{}: X.EOFBetweenMessages{}
    case Some{bytes}: X.BodyReceived{0, Bool.pick(U32, valid, 103, 0), bytes}


def input() -> X.Reception:
  physical(True{}, W.encode_body(W.Extension{W.PrepareRead{}, raw()}))


def invalid_input() -> X.Reception:
  physical(False{}, W.encode_body(W.Extension{W.PrepareRead{}, raw()}))


def primitives() -> Dispatch.Primitives:
  Dispatch.Primitives{V.CheckerPending{}, V.AllocatorPending{}, V.SealPending{}, N.CleanupPending{}, Dispatch.ArtifactPending{}, Execution.StartPending{}, V.SendComplete{}}


def job() -> Engine.Job:
  Engine.Job{input(), primitives()}


def authenticated_before() -> E.Snapshot:
  E.Snapshot{"fixture", D.State{[], [D.Row{"user", [D.Field{"credential", D.VText{"secret"}}, D.Field{"id", D.VText{"user"}}, D.Field{"kind", D.VText{"reader"}}]}]}, [], []}


def credentialed() -> P.Request:
  P.Request{"secret", "missing", D.VAbsent{}, "not-empty"}


def cached_raw() -> P.Request:
  P.Request{"secret", "missing", D.VAbsent{}, ""}


def context() -> D.Context:
  D.Context{"user", "reader"}
