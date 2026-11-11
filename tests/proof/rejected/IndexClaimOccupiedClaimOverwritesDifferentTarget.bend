# Deliberately false input-content claim; must reject at the proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/Index.bend as I
import ../../../library/Key.bend as K
import ../../../src/Termination.bend as T
import ../../../library/IndexEntryProofs.bend as Entry
import ../../../library/IndexClaimProofs.bend as Claim

def collection() -> D.Collection: D.Application{"index"}

def schema() -> D.Schema: D.Schema{[Entry.schema("index")]}

def state(rows: List<&2,D.Row>) -> D.State: D.State{[D.Table{"index",rows}],Nil{}}

def bool_done(value: Bool) -> S.Action: S.Finish{D.VBool{value}}

law false:
  {T.observe(3n,I.claim(collection(),["v"],"other",bool_done),schema(),state([I.unique(["v"],"stored")]),Nil{}) == S.Final{state([I.unique(["v"],"other")]),[S.OperationEvent{D.ViewExistence{collection(),K.encode(["v"])},S.Reading{D.Existence{True{}}}},S.OperationEvent{Claim.write(collection(),["v"],"other"),S.Write{}}],S.Response{S.Success{},D.VBool{True{}}}} : S.Trace}
def false(): {==}
