import Base
import ../../../proof/service/phases/PhaseFixtures.bend as Fixture
import ../../../contract/Data.bend as D
import ../../../contract/PreparedLaws.bend as H
import ../../../contract/PreparedProtocol.bend as W
import ../../../contract/Protocol.bend as P
import ../../../proof/service/specification/ServiceLaws.bend as E
import ../../../proof/service/phases/PreparePhases.bend as V
import ../../../proof/service/phases/PrepareEvents.bend as Events
import ../../../proof/service/phases/PrepareOrder.bend as Order

law false_negative_DeliveryRollback:
  {V.snapshot(Events.success(V.PrepareMode{}, P.Request{"credential", "source", D.VAbsent{}, "proof"}, D.Context{"user", "member"}, Fixture.before(), Fixture.entry(), [33], V.SendInterrupted{[33]})) == Fixture.before() : E.Snapshot}
def false_negative_DeliveryRollback(): {==}
