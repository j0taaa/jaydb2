# Deliberately false receipt behavior; must reject at the proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/Receipts.bend as H
import ../../../src/Termination.bend as T

def bool_schema() -> D.Schema: D.Schema{[D.SchemaTable{"owner","id",[D.Column{"id",D.TextValue{},False{}},D.Column{"input",D.TextValue{},False{}},D.Column{"operation",D.TextValue{},False{}},D.Column{"result",D.Boolean{},False{}}]}]}

def fields(key: String,input: String,operation: String,result: D.Value) -> List<&2,D.Field>: [D.Field{"id",D.VText{key}},D.Field{"input",D.VText{input}},D.Field{"operation",D.VText{operation}},D.Field{"result",result}]

def row(input: String,operation: String,result: D.Value) -> D.Row: D.Row{"r",fields("r",input,operation,result)}

def state(rows: List<&2,D.Row>) -> D.State: D.State{[D.Table{"owner",rows}],Nil{}}

def done(r: S.Return) -> S.Action:
  match r:
    case S.Datum{D.Cell{value}}: S.Finish{value}
    case _: S.Refuse{D.VText{"bad result"}}

def missing() -> S.Action: S.Finish{D.VText{"miss"}}

def event(name: String,value: D.Observation) -> S.OperationEvent: S.OperationEvent{D.ReadCell{D.Application{"owner"},"r",name},S.Reading{value}}

def hit_events(value: D.Value) -> List<&2,S.OperationEvent>: [event("input",D.Cell{D.VText{"input"}}),event("operation",D.Cell{D.VText{"op"}}),event("result",D.Cell{value})]

law false:
  {T.observe(4n,H.bound("owner","r","op","input",missing(),done),bool_schema(),state([row("input","op",D.VBool{True{}})]),Nil{}) == S.Final{state([row("input","op",D.VBool{True{}})]),hit_events(D.VBool{True{}}),S.Response{S.Refusal{},D.VText{"invalid receipt"}}} : S.Trace}
def false(): {==}
