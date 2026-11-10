# Deliberately false functional claim; must reject at its proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../library/Index.bend as I
import ../../../library/TableLaws.bend as Law

def collection() -> D.Collection: D.Application{"index"}

def entry(key: String,tag: String,target: String) -> D.Row: I.entry(key,[tag],target)

def build(rows: List<&2,D.Row>) -> List<&2,D.Row>: rows

law false_reject_single_lookup_proves_whole_index:
  Law.ExactIndex(~build,D.Application{"base"},collection(),D.State{[D.Table{"base",[I.unique(["known"],"t")]},D.Table{"index",[I.unique(["known"],"t"),entry("z","other","extra")]}],Nil{}})
def false_reject_single_lookup_proves_whole_index(): {==}
