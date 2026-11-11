# Deliberately false FUNCTIONAL claim: reject at the proof body, not syntax.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../src/Termination.bend as T
import ../../../library/Mutation.bend as M

def collection() -> D.Collection: D.Application{"t"}

def row(+key: String,title: String) -> D.Row:
  D.Row{key,[D.Field{"id",D.VText{key}},D.Field{"title",D.VText{title}}]}

def rowschema() -> D.Schema:
  D.Schema{[D.SchemaTable{"t","id",[D.Column{"id",D.TextValue{},False{}},D.Column{"title",D.TextValue{},False{}}]}]}

def rowsstate(rows: List<&2,D.Row>) -> D.State:
  D.State{[D.Table{"t",rows}],Nil{}}

def bool_done(b: Bool) -> S.Action: S.Finish{D.VBool{b}}

def reject_all(obs: D.Observation) -> Bool: False{}

law false:
  {T.observe(3n,M.replace_if(~reject_all,collection(),row("k","new"),"title",bool_done),rowschema(),rowsstate([row("k","old")]),Nil{}) == S.Final{rowsstate([row("k","old")]),Nil{},S.Response{S.Success{},D.VBool{False{}}}} : S.Trace}
def false(): {==}
