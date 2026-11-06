# A handle cannot bypass current authentication.
import Base
import ../../../contract/PreparedRegistry.bend as G

law false_unauthenticated_handle_resolves:
  for instance: String
  for handle: String
  for entries: List<&2, G.Entry>
  for entry: G.Entry
  {G.resolve(False{}, instance, handle, entries) == G.Resolved{entry} : G.Resolution}
def false_unauthenticated_handle_resolves(instance, handle, entries, entry):
  {==}
