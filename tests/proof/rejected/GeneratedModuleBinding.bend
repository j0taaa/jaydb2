import Base
import ../../../proof/GeneratedModule.bend as M
import ../../../src/Generate.bend as G
import ../../../proof/GeneratedLiterals.bend as L

law false:
  {M.parse_links(5n, G.links("code")) == L.Literal{"other", M.links_declarations()} : L.Parsed}
def false():
  {==}
