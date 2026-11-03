# Configuration must name the environment actually frozen by the server.
# Identity is a host argument, never a client-selected value.
import Base
import ../contract/Semantics.bend as S
import ../contract/Requirements.bend as R

def is_valid(c: S.Configuration, identity: String) -> Bool:
  S.Configuration{e, ls, lim, +amb} = c
  R.configuration_is_valid(S.Configuration{e, ls, lim, amb}) && String.eq(amb, identity)
