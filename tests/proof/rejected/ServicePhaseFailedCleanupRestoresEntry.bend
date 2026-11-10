import Base
import ../../../proof/service/phases/InvalidationFixtures.bend as Fixture
import ../../../proof/service/specification/ServiceLaws.bend as E
import ../../../proof/service/model/FrameBounds.bend as B
import ../../../proof/service/phases/PreparePhases.bend as V
import ../../../proof/service/phases/InvalidationPhases.bend as N

law false_negative_FailedCleanupRestoresEntry:
  {N.snapshot(N.remove_and_cleanup(Fixture.before(), "handle", [33], N.CleanupFailed{"cleanup", True{}}, V.SendComplete{})) == Fixture.before() : E.Snapshot}
def false_negative_FailedCleanupRestoresEntry(): {==}
