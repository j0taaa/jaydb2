# Deliberately false state/frame/delta claim; must reject at the proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../library/Index.bend as I
import ../../../library/IndexReplacementProofs.bend as Replace

def collection() -> D.Collection: D.Application{"index"}

def base() -> D.Collection: D.Application{"base"}

def entry(key: String,target: String) -> D.Row: I.entry(key,["v"],target)

def state(index: List<&2,D.Row>,rows: List<&2,D.Row>) -> D.State: D.State{[D.Table{"base",rows},D.Table{"index",index}],Nil{}}

law false_reject_rebuild_replacement_changes_separate_base:
  {D.rows_collection(base(),Replace.state(collection(),state([entry("a","old")],[entry("b","business")]),[entry("a","old")],[entry("n","new")])) == Some{[entry("n","new")]} : Maybe<&2,List<&2,D.Row>>}
def false_reject_rebuild_replacement_changes_separate_base(): {==}
