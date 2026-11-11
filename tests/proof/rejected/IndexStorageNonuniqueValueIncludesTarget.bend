# Deliberately false functional claim; must reject at its proof body.
import Base
import ../../../library/IndexEntryProofs.bend as Entry
import ../../../contract/Data.bend as D
import ../../../library/Index.bend as I
import ../../../library/Key.bend as K

law false:
  {D.find_field(Entry.fields(I.nonunique(["x"],"t")),"value") == Some{D.VText{K.encode(["x","t"])}} : Maybe<&2,D.Value>}
def false(): {==}
