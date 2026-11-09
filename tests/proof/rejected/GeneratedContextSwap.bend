# Source reification must retain the authenticated principal and its kind.
import Base
import ../../../contract/Data.bend as D
import ../../../src/Generate.bend as G
import ../../../proof/GeneratedContext.bend as Parser

law false_generated_context_swaps_principal_and_kind:
  {Parser.parse(8n, 8n, G.context(D.Context{"alice", "admin"})) ==
    Parser.Context{D.Context{"admin", "alice"}, ""} : Parser.ContextRead}
def false_generated_context_swaps_principal_and_kind():
  {==}
