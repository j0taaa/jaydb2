# Deliberately false FUNCTIONAL claim: reject at the proof body, not syntax.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../contract/Requirements.bend as R

def row(+key: String,title: String) -> D.Row:
  D.Row{key,[D.Field{"id",D.VText{key}},D.Field{"title",D.VText{title}}]}

def rowschema() -> D.Schema:
  D.Schema{[D.SchemaTable{"t","id",[D.Column{"id",D.TextValue{},False{}},D.Column{"title",D.TextValue{},False{}}]}]}

def rowsstate(rows: List<&2,D.Row>) -> D.State:
  D.State{[D.Table{"t",rows}],Nil{}}

law false:
  {S.publish(R.finalize(S.Response{S.Refusal{},D.VAbsent{}},S.Configuration{rowschema(),S.NoneLaw{},S.Limits{0n,0n,0n},"test"},rowsstate([row("k","first")])),rowsstate(Nil{}),rowsstate([row("k","first")])) == rowsstate([row("k","first")]) : D.State}
def false(): {==}
