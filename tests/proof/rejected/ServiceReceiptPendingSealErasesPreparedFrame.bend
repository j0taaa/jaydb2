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

law false_negative_PendingSealErasesPreparedFrame:
  {B.query(V.PreparationEvent, V.events(V.run(Fixture.configuration(), V.ReadMode{}, Fixture.raw(), Fixture.missing(),
    V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{Fixture.handle()}, V.SealPending{}, V.SendComplete{}})), 4n) == None{} : Maybe<&2, V.PreparationEvent>}
def false_negative_PendingSealErasesPreparedFrame(): {==}
