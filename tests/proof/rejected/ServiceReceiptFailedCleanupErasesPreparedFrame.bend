# Concrete phase branches, including stops after the prepared frame. These
# DATA returns do not assert a native checker/file or serial registry origin.
import Base
import ../../../contract/PreparedProtocol.bend as W
import ../../../contract/Resources.bend as X
import ../../../proof/service/phases/PreparePhases.bend as V
import ../../../proof/service/phases/InvalidationPhases.bend as N
import ../../../proof/service/model/FrameBounds.bend as B
import ../service-fixtures/Resolution.bend as Fixture

import ../service-fixtures/ReceiptFrames.bend as Example

law false_negative_FailedCleanupErasesPreparedFrame:
  {B.query(N.InvalidationEvent, N.events(N.run(Fixture.configuration(), Fixture.before(), Fixture.raw(), N.CleanupFailed{"late", False{}}, V.SendComplete{})), 2n) == None{} : Maybe<&2, N.InvalidationEvent>}
def false_negative_FailedCleanupErasesPreparedFrame(): {==}
