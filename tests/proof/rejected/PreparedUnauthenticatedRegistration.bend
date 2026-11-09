# Even an ostensibly admitted/sealed candidate cannot bypass current auth.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/PreparedLaws.bend as H
import ../../../contract/PreparedProtocol.bend as W
import ../../../contract/PreparedRegistry.bend as G
import ../../../contract/Protocol.bend as P
import ../../../contract/Semantics.bend as S
import ../../../proof/PreparedControlDispatch.bend as C

law false_unauthenticated_preparation_registers:
  for c: S.Configuration
  for +entry: G.Entry
  {C.prepare(c, D.State{Nil{}, Nil{}}, P.Request{"missing", "source", D.VAbsent{}, "proof"},
    Nil{}, C.Candidate{entry, True{}}) ==
    H.ControlResult{D.State{Nil{}, Nil{}}, Con{entry, Nil{}},
      H.Metadata{W.PreparedReceipt{G.handle(entry)}}} : H.ControlResult}
def false_unauthenticated_preparation_registers(c, entry):
  {==}
