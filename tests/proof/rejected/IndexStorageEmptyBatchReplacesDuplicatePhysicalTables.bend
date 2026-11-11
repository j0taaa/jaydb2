# Deliberately false state/frame/delta claim; must reject at the proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../library/Index.bend as I
import ../../../library/IndexValidatedWrites.bend as Batch

def collection() -> D.Collection: D.Application{"index"}

def entry(key: String,target: String) -> D.Row: I.entry(key,["v"],target)

def duplicate() -> D.State: D.State{[D.Table{"index",[entry("a","first")]},D.Table{"index",[entry("b","second")]}],Nil{}}

law false:
  {Batch.working(Nil{},collection(),duplicate(),[entry("a","first")]) == D.swap_collection(collection(),duplicate(),[entry("a","first")]) : D.State}
def false(): {==}
