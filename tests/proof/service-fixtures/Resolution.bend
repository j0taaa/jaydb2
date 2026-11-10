# Pure decoder/dispatch fixtures with an explicit current registry. They do
# not claim that its entry has actual serial origin, an original certificate,
# a native executable or Intact evidence; those are derived/required later.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/PreparedRegistry.bend as G
import ../../../contract/PreparedProtocol.bend as W
import ../../../contract/Protocol.bend as P
import ../../../contract/Resources.bend as X
import ../../../contract/Semantics.bend as S
import ../../../proof/service/specification/ServiceLaws.bend as E
import ../../../proof/service/phases/PreparePhases.bend as V
import ../../../proof/service/phases/InvalidationPhases.bend as N
import ../../../proof/service/model/serial/Dispatch.bend as Dispatch
import ../../../proof/service/model/serial/ExecutionPhases.bend as Execution
import ./Header.bend as Header


def configuration() -> S.Configuration:
  S.Configuration{D.Schema{[]}, S.NoneLaw{}, S.Limits{256n, 256n, 256n}, "fixture"}


def handle() -> String:
  "0000000000000000000000000000000000000000000000000000000000000000"


def entry() -> G.Entry:
  G.Entry{"fixture", handle(), "client", "proof", False{}, "stored"}


def raw() -> P.Request:
  P.Request{"secret", handle(), D.VAbsent{}, ""}


def before() -> E.Snapshot:
  E.Snapshot{"fixture", E.database(Header.authenticated_before()), [], [entry()]}


def missing() -> E.Snapshot:
  E.Snapshot{"fixture", E.database(Header.authenticated_before()), [], []}


def physical(encoded: Maybe<&2, List<&2, U32>>) -> X.Reception:
  match encoded:
    case None{}: X.EOFBetweenMessages{}
    case Some{bytes}: X.BodyReceived{0, 173, bytes}


def input() -> X.Reception:
  physical(W.encode_body(W.Extension{W.Execute{}, raw()}))


def primitives(artifact: Dispatch.ArtifactReturn) -> Dispatch.Primitives:
  Dispatch.Primitives{V.CheckerPending{}, V.AllocatorPending{}, V.SealPending{}, N.CleanupPending{}, artifact, Execution.StartPending{}, V.SendComplete{}}
