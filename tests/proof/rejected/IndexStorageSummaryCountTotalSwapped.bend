# Deliberately false functional claim; must reject at its proof body.
import Base
import ../../../library/IndexEntryProofs.bend as Entry
import ../../../contract/Data.bend as D
import ../../../library/Summary.bend as Summary
import ../../../library/Value.bend as V

law false_reject_summary_count_total_swapped:
  {D.find_field(Entry.fields(Summary.row("s",Summary.Stats{V.Int64{0,2},V.Int64{0,7}})),"total") == Some{D.VInt{0,2}} : Maybe<&2,D.Value>}
def false_reject_summary_count_total_swapped(): {==}
