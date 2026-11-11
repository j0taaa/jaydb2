# Deliberately false FUNCTIONAL claim: reject at the proof body, not syntax.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../src/Termination.bend as T
import ../../../library/Mutation.bend as M

def collection() -> D.Collection: D.Application{"t"}

def row(+key: String,title: String) -> D.Row:
  D.Row{key,[D.Field{"id",D.VText{key}},D.Field{"title",D.VText{title}}]}

def rowsstate(rows: List<&2,D.Row>) -> D.State:
  D.State{[D.Table{"t",rows}],Nil{}}

def bool_done(b: Bool) -> S.Action: S.Finish{D.VBool{b}}

law false:
  {T.observe(3n,M.insert_if_absent(collection(),row("k","new"),bool_done),D.Schema{Nil{}},rowsstate(Nil{}),Nil{}) == S.Final{rowsstate(Nil{}),[S.OperationEvent{D.ViewExistence{collection(),"k"},S.ErrorOfData{}}],S.Response{S.Success{},D.VBool{True{}}}} : S.Trace}
def false(): {==}
