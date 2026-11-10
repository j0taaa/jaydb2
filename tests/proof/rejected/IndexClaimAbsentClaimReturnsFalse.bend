# Deliberately false input-content claim; must reject at the proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/Index.bend as I
import ../../../src/Termination.bend as T
import ../../../library/IndexEntryProofs.bend as Entry
import ../../../library/IndexClaimProofs.bend as Claim

def collection() -> D.Collection: D.Application{"index"}

def schema() -> D.Schema: D.Schema{[Entry.schema("index")]}

def state(rows: List<&2,D.Row>) -> D.State: D.State{[D.Table{"index",rows}],Nil{}}

def bool_done(value: Bool) -> S.Action: S.Finish{D.VBool{value}}

law false_reject_absent_claim_returns_false:
  {T.observe(3n,I.claim(collection(),["v"],"new",bool_done),schema(),state(Nil{}),Nil{}) == S.Final{state([I.unique(["v"],"new")]),Claim.new_events(collection(),["v"],"new",Nil{}),S.Response{S.Success{},D.VBool{False{}}}} : S.Trace}
def false_reject_absent_claim_returns_false(): {==}
