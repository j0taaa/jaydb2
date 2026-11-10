import Base
import ../../../proof/service/phases/PreparePhases.bend as V
import ../../../proof/service/phases/InvalidationPhases.bend as N
import ../../../proof/service/model/FrameBounds.bend as B
import ../service-fixtures/Resolution.bend as Fixture

law false_negative_FailedCleanupErasesReceipt:
  {B.query(N.InvalidationEvent, N.events(N.run(Fixture.configuration(), Fixture.before(), Fixture.raw(), N.CleanupFailed{"late", False{}}, V.SendComplete{})), 2n) == None{} : Maybe<&2, N.InvalidationEvent>}
def false_negative_FailedCleanupErasesReceipt():
  {==}
