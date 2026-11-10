# Deliberately false state/frame/delta claim; must reject at the proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../library/Index.bend as I

def collection() -> D.Collection: D.Application{"index"}

def base() -> D.Collection: D.Application{"base"}

def entry(key: String,target: String) -> D.Row: I.entry(key,["v"],target)

def state(index: List<&2,D.Row>,rows: List<&2,D.Row>) -> D.State: D.State{[D.Table{"base",rows},D.Table{"index",index}],Nil{}}

law false_reject_frame_without_separate_collection:
  {D.rows_collection(collection(),D.swap_collection(collection(),state([entry("a","old")],Nil{}),[entry("n","new")])) == Some{[entry("a","old")]} : Maybe<&2,List<&2,D.Row>>}
def false_reject_frame_without_separate_collection(): {==}
