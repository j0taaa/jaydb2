# Invalidation removes every matching handle, including malformed duplicates.
import Base
import ../../../contract/PreparedRegistry.bend as G

law false_invalidated_handle_is_available:
  {G.lookup("instance", "handle", G.remove("instance", "handle",
    [G.Entry{"instance", "handle", "source", "proof", False{}, "seal"}])) ==
    Some{G.Entry{"instance", "handle", "source", "proof", False{}, "seal"}} : Maybe<&2, G.Entry>}
def false_invalidated_handle_is_available():
  {==}
