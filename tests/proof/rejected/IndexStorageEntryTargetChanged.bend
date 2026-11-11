# Deliberately false functional claim; must reject at its proof body.
import Base
import ../../../library/IndexEntryProofs.bend as Entry
import ../../../contract/Data.bend as D
import ../../../library/Index.bend as I

law false:
  {D.find_field(Entry.fields(I.unique(["x"],"target")),"target") == Some{D.VText{"other"}} : Maybe<&2,D.Value>}
def false(): {==}
