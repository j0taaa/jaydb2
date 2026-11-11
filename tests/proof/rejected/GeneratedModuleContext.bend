import Base
import ../../../proof/GeneratedModule.bend as M
import ../../../src/Generate.bend as G
import ../../../contract/Data.bend as D

law false:
  {M.parse_instance(2n, 2n, 3n, G.instance_content(D.Context{"x", "y"}, [0], 0, 1)) ==
   M.ModuleInstance{D.Context{"y", "x"}, D.VAbsent{}, "\n"} : M.ModuleRead}
def false():
  {==}
