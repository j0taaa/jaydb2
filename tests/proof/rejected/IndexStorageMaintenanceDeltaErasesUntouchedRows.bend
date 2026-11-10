# Deliberately false state/frame/delta claim; must reject at the proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../library/Index.bend as I
import ../../../library/IndexMaintenancePlan.bend as Maint

def entry(key: String,target: String) -> D.Row: I.entry(key,["v"],target)

law false_reject_maintenance_delta_erases_untouched_rows:
  {Maint.rows(["a"],[entry("n","new")],[entry("a","old"),entry("b","untouched")]) == [entry("n","new")] : List<&2,D.Row>}
def false_reject_maintenance_delta_erases_untouched_rows(): {==}
