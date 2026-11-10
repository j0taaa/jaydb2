import Base
import ../../../contract/Data.bend as D
import ../../../contract/PreparedProtocol.bend as W
import ../../../proof/service/phases/PreparePhases.bend as V
import ../../../proof/service/model/FrameBounds.bend as B
import ../service-fixtures/Resolution.bend as Fixture

law false_negative_WrongAcceptanceContext:
  {B.query(V.PreparationEvent, V.events(V.run(Fixture.configuration(), V.ReadMode{}, Fixture.raw(), Fixture.missing(), V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{Fixture.handle()}, V.SealPending{}, V.SendComplete{}})), 2n) == Some{V.Accepted{W.Extension{W.PrepareRead{}, Fixture.raw()}, D.Context{"intruder", "reader"}}} : Maybe<&2, V.PreparationEvent>}
def false_negative_WrongAcceptanceContext():
  {==}
