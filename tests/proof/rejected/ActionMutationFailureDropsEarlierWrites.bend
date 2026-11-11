# Deliberately false FUNCTIONAL claim: reject at the proof body, not syntax.
import Base
import ../../../library/MutationBooleanDecisions.bend as Boolean
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../src/Termination.bend as T
import ../../../library/Action.bend as A

def collection() -> D.Collection: D.Application{"t"}

def row(+key: String,title: String) -> D.Row:
  D.Row{key,[D.Field{"id",D.VText{key}},D.Field{"title",D.VText{title}}]}

def rowschema() -> D.Schema:
  D.Schema{[D.SchemaTable{"t","id",[D.Column{"id",D.TextValue{},False{}},D.Column{"title",D.TextValue{},False{}}]}]}

def rowsstate(rows: List<&2,D.Row>) -> D.State:
  D.State{[D.Table{"t",rows}],Nil{}}

law false:
  {T.observe(3n,A.define_rows(collection(),[row("k","first"),D.Row{"bad",Nil{}}],S.Finish{D.VAbsent{}}),rowschema(),rowsstate(Nil{}),Nil{}) == S.Final{rowsstate([row("k","first")]),[S.OperationEvent{D.DefineRow{collection(),D.row_key(D.Row{"bad",Nil{}}),Boolean.row_fields(D.Row{"bad",Nil{}})},S.ErrorOfData{}}],S.Response{S.DataError{},D.VAbsent{}}} : S.Trace}
def false(): {==}
