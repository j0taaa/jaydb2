# Deliberately false state/frame/delta claim; must reject at the proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../library/Index.bend as I
import ../../../library/RowInsertionProofs.bend as Insert

def entry(key: String,target: String) -> D.Row: I.entry(key,["v"],target)

law false_reject_unsorted_upserts_retain_supplied_order:
  {Insert.all([entry("b","second"),entry("a","first")],Nil{}) == [entry("b","second"),entry("a","first")] : List<&2,D.Row>}
def false_reject_unsorted_upserts_retain_supplied_order(): {==}
