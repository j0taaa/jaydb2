# Deliberately false state/frame/delta claim; must reject at the proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../library/Index.bend as I
import ../../../library/IndexEntryProofs.bend as Entry

def entry(key: String,target: String) -> D.Row: I.entry(key,["v"],target)

law false:
  {D.rows_valid_cases([entry("a","first"),entry("a","second")],Entry.schema("index")) == True{} : Bool}
def false(): {==}
