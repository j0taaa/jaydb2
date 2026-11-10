import Base
import ../../../proof/service/phases/InvalidationFixtures.bend as Fixture
import ../../../proof/service/specification/ServiceLaws.bend as E
import ../../../proof/service/model/FrameBounds.bend as B
import ../../../proof/service/phases/PreparePhases.bend as V
import ../../../proof/service/phases/InvalidationPhases.bend as N

law false_negative_CleanupFailureLosesMutation:
  {B.query(N.InvalidationEvent, N.events(N.remove_and_cleanup(Fixture.before(), "handle", [33], N.CleanupFailed{"cleanup", True{}}, V.SendComplete{})), 0n) == None{} : Maybe<&2, N.InvalidationEvent>}
def false_negative_CleanupFailureLosesMutation(): {==}
