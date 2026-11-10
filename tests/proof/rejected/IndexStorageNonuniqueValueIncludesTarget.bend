# Deliberately false functional claim; must reject at its proof body.
import Base
import ../../../library/IndexEntryProofs.bend as Entry
import ../../../contract/Data.bend as D
import ../../../library/Index.bend as I
import ../../../library/Key.bend as K

law false_reject_nonunique_value_includes_target:
  {D.find_field(Entry.fields(I.nonunique(["x"],"t")),"value") == Some{D.VText{K.encode(["x","t"])}} : Maybe<&2,D.Value>}
def false_reject_nonunique_value_includes_target(): {==}
