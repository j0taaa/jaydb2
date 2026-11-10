import Base
import ../../../contract/PreparedProtocol.bend as W
import ../../../contract/Resources.bend as X
import ../service-fixtures/Resolution.bend as Fixture

def bytes(encoded: Maybe<&2, List<&2, U32>>) -> List<&2, U32>:
  match encoded:
    case None{}: []
    case Some{body}: body

law false_negative_InventPhysicalReception:
  {X.reception_is_valid(X.BodyReceived{0, 0, bytes(W.encode_body(W.Extension{W.Invalidate{}, Fixture.raw()}))}) == True{} : Bool}
def false_negative_InventPhysicalReception():
  {==}
