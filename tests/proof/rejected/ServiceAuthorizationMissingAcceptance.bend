import Base
import ../../../proof/service/phases/PreparePhases.bend as V
import ../../../proof/service/model/FrameBounds.bend as B
import ../service-fixtures/Resolution.bend as Fixture

law false_negative_MissingAcceptance:
  {B.query(V.PreparationEvent, V.events(V.run(Fixture.configuration(), V.ReadMode{}, Fixture.raw(), Fixture.missing(), V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{Fixture.handle()}, V.SealPending{}, V.SendComplete{}})), 2n) == None{} : Maybe<&2, V.PreparationEvent>}
def false_negative_MissingAcceptance():
  {==}
