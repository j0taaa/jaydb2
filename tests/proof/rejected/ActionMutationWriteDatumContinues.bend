# Deliberately false FUNCTIONAL claim: reject at the proof body, not syntax.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/Action.bend as A

def collection() -> D.Collection: D.Application{"t"}

law false_reject_write_datum_continues:
  {A.written(S.Access{D.RemoveRow{collection(),"next"},r => S.Finish{D.VAbsent{}}},S.Datum{D.Cell{D.VAbsent{}}}) == S.Access{D.RemoveRow{collection(),"next"},r => S.Finish{D.VAbsent{}}} : S.Action}
def false_reject_write_datum_continues(): {==}
