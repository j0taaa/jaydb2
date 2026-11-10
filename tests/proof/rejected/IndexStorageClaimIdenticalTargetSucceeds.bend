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

def state(rows: List<&2,D.Row>) -> D.State: D.State{[D.Table{"index",rows}],Nil{}}

def bool_done(value: Bool) -> S.Action: S.Finish{D.VBool{value}}

law false_reject_claim_identical_target_succeeds:
  {T.observe(3n,I.claim(collection(),["known"],"t",bool_done),schema(),state([I.unique(["known"],"t")]),Nil{}) == S.Final{state([I.unique(["known"],"t")]),[S.OperationEvent{D.ViewExistence{collection(),K.encode(["known"])},S.Reading{D.Existence{True{}}}}],S.Response{S.Success{},D.VBool{True{}}}} : S.Trace}
def false_reject_claim_identical_target_succeeds(): {==}
