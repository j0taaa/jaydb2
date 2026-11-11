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
  {T.observe(4n,I.rebuild(collection(),[entry("b","yes","b"),entry("a","yes","a")],S.Finish{D.VAbsent{}}),schema(),state(Nil{}),Nil{}) == S.Final{state([entry("b","yes","b"),entry("a","yes","a")]),[S.OperationEvent{D.EnumerateKeys{collection()},S.Reading{D.Keys{[]}}},S.OperationEvent{D.DefineRow{collection(),"b",Entry.fields(entry("b","yes","b"))},S.Write{}},S.OperationEvent{D.DefineRow{collection(),"a",Entry.fields(entry("a","yes","a"))},S.Write{}}],S.Response{S.Success{},D.VAbsent{}}} : S.Trace}
def false(): {==}
