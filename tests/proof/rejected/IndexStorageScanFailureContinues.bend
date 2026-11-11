# Deliberately false functional claim; must reject at its proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/Index.bend as I
import ../../../src/Termination.bend as T

def collection() -> D.Collection: D.Application{"index"}

def bad_schema() -> D.Schema:
  D.Schema{[D.SchemaTable{"index","id",[D.Column{"id",D.TextValue{},False{}},D.Column{"target",D.TextValue{},False{}}]}]}

def entry(key: String,tag: String,target: String) -> D.Row: I.entry(key,[tag],target)

def state(rows: List<&2,D.Row>) -> D.State: D.State{[D.Table{"index",rows}],Nil{}}

def done(value: D.Value) -> S.Action: S.Finish{value}

law false:
  {T.observe(8n,I.scan_equal(collection(),["yes"],done),bad_schema(),state([entry("a","yes","first"),entry("b","no","skipped"),entry("c","yes","last")]),Nil{}) == S.Final{state([entry("a","yes","first"),entry("b","no","skipped"),entry("c","yes","last")]),[S.OperationEvent{D.EnumerateKeys{collection()},S.Reading{D.Keys{["a","b","c"]}}},S.OperationEvent{D.ReadCell{collection(),"a","target"},S.Reading{D.Cell{D.VText{"first"}}}},S.OperationEvent{D.ReadCell{collection(),"a","value"},S.ErrorOfData{}},S.OperationEvent{D.ReadCell{collection(),"b","target"},S.Reading{D.Cell{D.VText{"skipped"}}}}],S.Response{S.DataError{},D.VAbsent{}}} : S.Trace}
def false(): {==}
