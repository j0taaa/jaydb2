# Deliberately false receipt behavior; must reject at the proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/Receipts.bend as H
import ../../../src/Termination.bend as T

def no_input_schema() -> D.Schema: D.Schema{[D.SchemaTable{"owner","id",[D.Column{"id",D.TextValue{},False{}}]}]}

def state(rows: List<&2,D.Row>) -> D.State: D.State{[D.Table{"owner",rows}],Nil{}}

def done(r: S.Return) -> S.Action:
  match r:
    case S.Datum{D.Cell{value}}: S.Finish{value}
    case _: S.Refuse{D.VText{"bad result"}}

def missing() -> S.Action: S.Finish{D.VText{"miss"}}

law false:
  {T.observe(4n,H.bound("owner","r","op","input",missing(),done),no_input_schema(),state(Nil{}),Nil{}) == S.Final{state(Nil{}),[S.OperationEvent{D.ReadCell{D.Application{"owner"},"r","input"},S.ErrorOfData{}}],S.Response{S.Success{},D.VText{"miss"}}} : S.Trace}
def false(): {==}
