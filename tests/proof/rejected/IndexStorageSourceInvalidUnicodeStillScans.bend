# Deliberately false source/domain/indexed-content claim. Proof-body failure.
import Base
import ../../../library/IndexSourceRows.bend as Source
import ../../../library/IndexEntryProofs.bend as Entry
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/Index.bend as I
import ../../../src/Termination.bend as T

def e(key: String,parts: List<&2,String>,target: String) -> Source.SourceEntry: Source.SourceEntry{key,parts,target}

def collection() -> D.Collection: D.Application{"index"}

def schema() -> D.Schema: D.Schema{[Entry.schema("index")]}

def state(entries: List<&2,Source.SourceEntry>) -> D.State: D.State{[D.Table{"index",Source.rows(entries)}],Nil{}}

def finish(value: D.Value) -> S.Action: S.Finish{value}

def bad() -> Source.SourceEntry: e(SCon{Chr{55296},SNil{}},["yes"],"t")

law false:
  {T.observe(4n,I.scan_equal(collection(),["yes"],finish),schema(),state([bad()]),Nil{}) == S.Final{state([bad()]),[S.OperationEvent{D.EnumerateKeys{collection()},S.Reading{D.Keys{Source.keys([bad()])}}},S.OperationEvent{D.ReadCell{collection(),Source.key(bad()),"target"},S.ErrorOfData{}}],S.Response{S.Success{},D.VList{D.VText{"t"},D.VListEmpty{}}}} : S.Trace}
def false(): {==}
