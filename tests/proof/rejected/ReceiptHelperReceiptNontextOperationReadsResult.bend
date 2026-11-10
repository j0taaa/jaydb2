# Deliberately false receipt behavior; must reject at the proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/Receipts.bend as H

def done(r: S.Return) -> S.Action:
  match r:
    case S.Datum{D.Cell{value}}: S.Finish{value}
    case _: S.Refuse{D.VText{"bad result"}}

law false_reject_receipt_nontext_operation_reads_result:
  {H.operation_seen("owner","r","op",done,S.Datum{D.Cell{D.VBool{True{}}}}) == S.Access{D.ReadCell{D.Application{"owner"},"r","result"},done} : S.Action}
def false_reject_receipt_nontext_operation_reads_result(): {==}
