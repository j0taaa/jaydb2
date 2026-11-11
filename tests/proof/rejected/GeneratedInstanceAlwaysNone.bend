# Valid, measured input cannot be discarded under a vacuous failure contract.
import Base
import ../../../src/Generate.bend as G
import ../../../contract/Data.bend as D

law false:
  {G.instance(D.Context{"", ""}, D.VAbsent{}) == None{} : Maybe<&2, String>}
def false():
  {==}
