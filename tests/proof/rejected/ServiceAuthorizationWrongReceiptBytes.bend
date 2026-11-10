import Base
import ../../../contract/PreparedProtocol.bend as W
import ../../../proof/service/phases/PreparePhases.bend as V
import ../../../proof/service/model/FrameBounds.bend as B
import ../service-fixtures/Resolution.bend as Fixture

law false_negative_WrongReceiptBytes:
  {B.query(V.PreparationEvent, V.events(V.run(Fixture.configuration(), V.ReadMode{}, Fixture.raw(), Fixture.missing(), V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{Fixture.handle()}, V.SealPending{}, V.SendComplete{}})), 4n) == Some{V.ReceiptPrepared{W.PreparedReceipt{Fixture.handle()}, [0]}} : Maybe<&2, V.PreparationEvent>}
def false_negative_WrongReceiptBytes():
  {==}
