# Deliberately false FUNCTIONAL claim: reject at the proof body, not syntax.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../src/Core.bend as Core

def row(+key: String,title: String) -> D.Row:
  D.Row{key,[D.Field{"id",D.VText{key}},D.Field{"title",D.VText{title}}]}

def rowsstate(rows: List<&2,D.Row>) -> D.State:
  D.State{[D.Table{"t",rows}],Nil{}}

law false_reject_core_refusal_publishes_working:
  {Core.conclude(Core.Prepared{rowsstate([row("k","first")]),Nil{},S.Response{S.Refusal{},D.VAbsent{}},Nil{}},rowsstate(Nil{})) == Core.Conclusion{rowsstate([row("k","first")]),S.Response{S.Refusal{},D.VAbsent{}},Nil{}} : Core.Conclusion}
def false_reject_core_refusal_publishes_working(): {==}
