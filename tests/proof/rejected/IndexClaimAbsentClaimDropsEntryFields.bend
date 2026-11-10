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

law false_reject_absent_claim_drops_entry_fields:
  {T.observe(3n,I.claim(collection(),["v"],"new",bool_done),schema(),state(Nil{}),Nil{}) == S.Final{state([D.Row{K.encode(["v"]),[D.Field{"id",D.VText{K.encode(["v"])}}]}]),Claim.new_events(collection(),["v"],"new",Nil{}),S.Response{S.Success{},D.VBool{True{}}}} : S.Trace}
def false_reject_absent_claim_drops_entry_fields(): {==}
