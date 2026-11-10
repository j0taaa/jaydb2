# Deliberately false receipt behavior; must reject at the proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/Receipts.bend as H

def fields(key: String,input: String,operation: String,result: D.Value) -> List<&2,D.Field>: [D.Field{"id",D.VText{key}},D.Field{"input",D.VText{input}},D.Field{"operation",D.VText{operation}},D.Field{"result",result}]

law false_reject_receipt_put_is_partial_column_write:
  {H.put("owner","r",fields("r","input","op",D.VText{"stored"}),S.Finish{D.VText{"written"}}) == S.Access{D.DefineColumn{D.Application{"owner"},"r","input",D.VText{"input"}},H.written(S.Finish{D.VText{"written"}})} : S.Action}
def false_reject_receipt_put_is_partial_column_write(): {==}
