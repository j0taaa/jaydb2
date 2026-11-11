# Deliberately false receipt behavior; must reject at the proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/Receipts.bend as H
import ../../../src/Termination.bend as T

def columns() -> List<&2,D.Column>: [D.Column{"id",D.TextValue{},False{}},D.Column{"input",D.TextValue{},False{}},D.Column{"operation",D.TextValue{},False{}},D.Column{"result",D.TextValue{},False{}}]

def schema() -> D.Schema: D.Schema{[D.SchemaTable{"owner","id",columns()}]}

def state(rows: List<&2,D.Row>) -> D.State: D.State{[D.Table{"owner",rows}],Nil{}}

def done(r: S.Return) -> S.Action:
  match r:
    case S.Datum{D.Cell{value}}: S.Finish{value}
    case _: S.Refuse{D.VText{"bad result"}}

def missing() -> S.Action: S.Finish{D.VText{"miss"}}

def event(name: String,value: D.Observation) -> S.OperationEvent: S.OperationEvent{D.ReadCell{D.Application{"owner"},"r",name},S.Reading{value}}

law false:
  {T.observe(4n,H.bound("owner","r","op","input",missing(),done),schema(),state([D.Row{"r",[D.Field{"id",D.VText{"r"}},D.Field{"input",D.VText{"input"}},D.Field{"operation",D.VText{"op"}}]}]),Nil{}) == S.Final{state([D.Row{"r",[D.Field{"id",D.VText{"r"}},D.Field{"input",D.VText{"input"}},D.Field{"operation",D.VText{"op"}}]}]),[event("input",D.Cell{D.VText{"input"}}),event("operation",D.Cell{D.VText{"op"}}),event("result",D.RowAbsent{})],S.Response{S.Refusal{},D.VText{"bad result"}}} : S.Trace}
def false(): {==}
