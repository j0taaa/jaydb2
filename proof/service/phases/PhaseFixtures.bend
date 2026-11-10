import Base
import ../../../contract/Data.bend as D
import ../../../contract/PreparedLaws.bend as H
import ../../../contract/PreparedProtocol.bend as W
import ../../../contract/PreparedRegistry.bend as G
import ../../../contract/Protocol.bend as P
import ../../../contract/Semantics.bend as S
import ../specification/ServiceLaws.bend as E
import ./PreparePhases.bend as V
import ./PrepareEvents.bend as Events
import ./PrepareOrder.bend as Order
import ./PrepareFailures.bend as Failures

def before() -> E.Snapshot:
  E.Snapshot{"instance", D.State{Nil{}, Nil{}}, [11, 22], Nil{}}

def entry() -> G.Entry:
  G.Entry{"instance", "handle", "source", "proof", False{}, "seal"}

def wire() -> W.WireRequest:
  W.Extension{W.Prepare{}, P.Request{"credential", "source", D.VAbsent{}, "proof"}}

def prefix() -> List<&2, V.PreparationEvent>:
  [V.WireReceived{wire()}, V.IdentityEstablished{wire(), None{}},
    V.Accepted{wire(), D.Context{"user", "member"}}, V.HandleChosen{"handle"}]

law receipt_is_needed_before_sealing:
  {Order.ordered([V.ArtifactSealed{entry()}], Order.ReadyReceipt{}) == False{} : Bool}
def receipt_is_needed_before_sealing(): {==}

law delivery_interruption_keeps_the_registered_entry:
  {V.snapshot(Events.success(V.PrepareMode{}, P.Request{"credential", "source", D.VAbsent{}, "proof"}, D.Context{"user", "member"},
    before(), entry(), [33], V.SendInterrupted{[33]})) ==
    E.Snapshot{"instance", D.State{Nil{}, Nil{}}, [11, 22], [entry()]} : E.Snapshot}
def delivery_interruption_keeps_the_registered_entry(): {==}

law no_event_is_allowed_after_closure:
  {Order.ordered([V.Closed{}, V.Delivered{[33]}], Order.ReadyClose{}) == False{} : Bool}
def no_event_is_allowed_after_closure(): {==}
