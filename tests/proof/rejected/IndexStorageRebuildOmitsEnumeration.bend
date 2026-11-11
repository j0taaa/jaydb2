# Deliberately false functional claim; must reject at its proof body.
import Base
import ../../../library/IndexEntryProofs.bend as Entry
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/Index.bend as I
import ../../../src/Termination.bend as T

def collection() -> D.Collection: D.Application{"index"}

def schema() -> D.Schema: D.Schema{[Entry.schema("index")]}

def entry(key: String,tag: String,target: String) -> D.Row: I.entry(key,[tag],target)

def state(rows: List<&2,D.Row>) -> D.State: D.State{[D.Table{"index",rows}],Nil{}}

law false:
  {T.observe(5n,I.rebuild(collection(),[entry("n","yes","new")],S.Finish{D.VAbsent{}}),schema(),state([entry("a","yes","old-a"),entry("b","no","old-b")]),Nil{}) == S.Final{state([entry("n","yes","new")]),[S.OperationEvent{D.RemoveRow{collection(),"a"},S.Write{}},S.OperationEvent{D.RemoveRow{collection(),"b"},S.Write{}},S.OperationEvent{D.DefineRow{collection(),"n",Entry.fields(entry("n","yes","new"))},S.Write{}}],S.Response{S.Success{},D.VAbsent{}}} : S.Trace}
def false(): {==}
