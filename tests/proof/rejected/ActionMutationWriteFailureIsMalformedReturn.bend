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

def rowsstate(rows: List<&2,D.Row>) -> D.State:
  D.State{[D.Table{"t",rows}],Nil{}}

law false:
  {T.observe(2n,A.define_rows(collection(),[row("k","first")],S.Finish{D.VAbsent{}}),D.Schema{Nil{}},rowsstate(Nil{}),Nil{}) == S.Final{rowsstate(Nil{}),[S.OperationEvent{D.DefineRow{collection(),D.row_key(row("k","first")),Boolean.row_fields(row("k","first"))},S.ErrorOfData{}}],S.Response{S.Refusal{},D.VText{"unexpected write return"}}} : S.Trace}
def false(): {==}
