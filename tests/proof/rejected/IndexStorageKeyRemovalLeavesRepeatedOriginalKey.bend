# Deliberately false state/frame/delta claim; must reject at the proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../library/Index.bend as I
import ../../../library/RowRemovalProofs.bend as Remove

def entry(key: String,target: String) -> D.Row: I.entry(key,["v"],target)

law false:
  {Remove.all(D.keys_rows([entry("a","first"),entry("a","second")]),[entry("a","first"),entry("a","second")]) == [entry("a","second")] : List<&2,D.Row>}
def false(): {==}
