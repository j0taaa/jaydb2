# Deliberately false functional claim; must reject at its proof body.
import Base
import ../../../library/IndexEntryProofs.bend as Entry
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/Index.bend as I
import ../../../library/Key.bend as K
import ../../../src/Termination.bend as T

def collection() -> D.Collection: D.Application{"index"}

def schema() -> D.Schema: D.Schema{[Entry.schema("index")]}

def entry(key: String,tag: String,target: String) -> D.Row: I.entry(key,[tag],target)

def state(rows: List<&2,D.Row>) -> D.State: D.State{[D.Table{"index",rows}],Nil{}}

def done(value: D.Value) -> S.Action: S.Finish{value}

law false_reject_scan_deduplicates_targets:
  {T.observe(6n,I.scan_equal(collection(),["yes"],done),schema(),state([entry("a","yes","same"),entry("c","yes","same")]),Nil{}) == S.Final{state([entry("a","yes","same"),entry("c","yes","same")]),[S.OperationEvent{D.EnumerateKeys{collection()},S.Reading{D.Keys{["a","c"]}}},S.OperationEvent{D.ReadCell{collection(),"a","target"},S.Reading{D.Cell{D.VText{"same"}}}},S.OperationEvent{D.ReadCell{collection(),"a","value"},S.Reading{D.Cell{D.VText{K.encode(["yes"])}}}},S.OperationEvent{D.ReadCell{collection(),"c","target"},S.Reading{D.Cell{D.VText{"same"}}}},S.OperationEvent{D.ReadCell{collection(),"c","value"},S.Reading{D.Cell{D.VText{K.encode(["yes"])}}}}],S.Response{S.Success{},D.VList{D.VText{"same"},D.VListEmpty{}}}} : S.Trace}
def false_reject_scan_deduplicates_targets(): {==}
