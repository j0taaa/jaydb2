import Base
import ../../../proof/service/phases/InvalidationPhases.bend as N
import ../service-fixtures/Resolution.bend as Fixture
import ../../../contract/PreparedRegistry.bend as G
import ../../../proof/service/specification/ServiceLaws.bend as E

law false_negative_InvalidationKeepsEntryAfterRemoval:
  {E.registry(N.removed(Fixture.before(), Fixture.handle())) == [Fixture.entry()] : List<&2, G.Entry>}
def false_negative_InvalidationKeepsEntryAfterRemoval():
  {==}
