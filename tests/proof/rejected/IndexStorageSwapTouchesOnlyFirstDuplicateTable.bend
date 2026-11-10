# Deliberately false state/frame/delta claim; must reject at the proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../library/Index.bend as I

def collection() -> D.Collection: D.Application{"index"}

def entry(key: String,target: String) -> D.Row: I.entry(key,["v"],target)

def duplicate() -> D.State: D.State{[D.Table{"index",[entry("a","first")]},D.Table{"index",[entry("b","second")]}],Nil{}}

law false_reject_swap_touches_only_first_duplicate_table:
  {D.swap_collection(collection(),duplicate(),Nil{}) == D.State{[D.Table{"index",Nil{}},D.Table{"index",[entry("b","second")]}],Nil{}} : D.State}
def false_reject_swap_touches_only_first_duplicate_table(): {==}
