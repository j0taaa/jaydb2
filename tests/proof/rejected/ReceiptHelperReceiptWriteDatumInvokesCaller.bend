# Deliberately false receipt behavior; must reject at the proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/Receipts.bend as H



law false_reject_receipt_write_datum_invokes_caller:
  {H.written(S.Finish{D.VText{"written"}},S.Datum{D.Cell{D.VAbsent{}}}) == S.Finish{D.VText{"written"}} : S.Action}
def false_reject_receipt_write_datum_invokes_caller(): {==}
