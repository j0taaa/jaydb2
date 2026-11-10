# Deliberately false state/frame/delta claim; must reject at the proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../library/Index.bend as I
import ../../../library/IndexMaintenancePlan.bend as Maint

def entry(key: String,target: String) -> D.Row: I.entry(key,["v"],target)

law false_reject_maintenance_duplicate_upserts_first_wins:
  {Maint.rows(Nil{},[entry("n","first"),entry("n","last")],Nil{}) == [entry("n","first")] : List<&2,D.Row>}
def false_reject_maintenance_duplicate_upserts_first_wins(): {==}
