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

law false_negative_RegistrationBeforeReceipt:
  {Order.ordered([V.ArtifactSealed{Fixture.entry()}, V.RegistryChanged{Fixture.entry(), Fixture.before(), Fixture.before()}], Order.ReadyReceipt{}) == True{} : Bool}
def false_negative_RegistrationBeforeReceipt(): {==}
