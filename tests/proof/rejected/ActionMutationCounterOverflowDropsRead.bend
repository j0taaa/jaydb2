# Deliberately false FUNCTIONAL claim: reject at the proof body, not syntax.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../src/Termination.bend as T
import ../../../library/Mutation.bend as M
import ../../../library/Value.bend as V

def collection() -> D.Collection: D.Application{"t"}

def rowsstate(rows: List<&2,D.Row>) -> D.State:
  D.State{[D.Table{"t",rows}],Nil{}}

def counterschema(kind: D.ColumnKind) -> D.Schema:
  D.Schema{[D.SchemaTable{"t","id",[D.Column{"count",kind,False{}},D.Column{"id",D.TextValue{},False{}}]}]}

def counterstate(value: D.Value) -> D.State:
  rowsstate([D.Row{"k",[D.Field{"count",value},D.Field{"id",D.VText{"k"}}]}])

def int_done(x: V.Int64) -> S.Action: S.Finish{V.int_value(x)}

law false:
  {T.observe(3n,M.next(collection(),"k","count",int_done),counterschema(D.Integer{}),counterstate(D.VInt{2147483647,4294967295}),Nil{}) == S.Final{counterstate(D.VInt{2147483647,4294967295}),Nil{},S.Response{S.Refusal{},D.VText{"counter overflow"}}} : S.Trace}
def false(): {==}
