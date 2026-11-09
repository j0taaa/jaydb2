# A failed write does not undo an already applied control-registry mutation.
import Base
import ../../../contract/PreparedRegistry.bend as G
import ../../../proof/PreparedControlTrace.bend as T

law false_delivery_failure_erases_registered_entry:
  for +entry: G.Entry
  for bytes: List<&2, U32>
  {T.replay(T.send_events(T.Interrupted{Nil{}}, bytes), Con{entry, Nil{}}) == Nil{} : List<&2, G.Entry>}
def false_delivery_failure_erases_registered_entry(entry, bytes):
  {==}
