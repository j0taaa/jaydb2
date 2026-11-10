# Deliberately false receipt behavior; must reject at the proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/Receipts.bend as H
import ../../../src/Termination.bend as T

def columns() -> List<&2,D.Column>: [D.Column{"id",D.TextValue{},False{}},D.Column{"input",D.TextValue{},False{}},D.Column{"operation",D.TextValue{},False{}},D.Column{"result",D.TextValue{},False{}}]

def schema() -> D.Schema: D.Schema{[D.SchemaTable{"owner","id",columns()}]}

def state(rows: List<&2,D.Row>) -> D.State: D.State{[D.Table{"owner",rows}],Nil{}}

law false_reject_receipt_invalid_put_invokes_caller:
  {T.observe(2n,H.put("owner","r",Nil{},S.Finish{D.VText{"written"}}),schema(),state(Nil{}),Nil{}) == S.Final{state(Nil{}),[S.OperationEvent{D.DefineRow{D.Application{"owner"},"r",Nil{}},S.ErrorOfData{}}],S.Response{S.Success{},D.VText{"written"}}} : S.Trace}
def false_reject_receipt_invalid_put_invokes_caller(): {==}
