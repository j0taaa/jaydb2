# Causal negative: an old original certificate cannot authorize a revoked
# current handle. Removing the transition's current lookup condition is unsound.
import Base
import ../../../contract/PreparedRegistry.bend as G

law false_removed_handle_would_still_have_current_authority:
  for +instance: String
  for +handle: String
  for entries: List<&2, G.Entry>
  for -entry: G.Entry
  {G.lookup(instance, handle, G.remove(instance, handle, entries)) == Some{entry} : Maybe<&2, G.Entry>}
def false_removed_handle_would_still_have_current_authority(instance, handle, entries, entry):
  G.removed_handle_cannot_resolve(instance, handle, entries)
