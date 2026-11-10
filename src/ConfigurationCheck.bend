# Configuration must name the environment actually frozen by the server.
# Identity is a host argument, never a client-selected value.
import Base
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Semantics.bend as S
import ../contract/Requirements.bend as R

def is_valid(c: S.Configuration, identity: String) -> Bool:
  S.Configuration{e, ls, lim, +amb} = c
  R.configuration_is_valid(S.Configuration{e, ls, lim, amb}) && String.eq(amb, identity)

# Private worker protocol: success followed by the encoded initial state,
# or the refusal marker. The seed remains suspended until configuration passes.
def initial_packet(encoded: Maybe<&2, List<&2, U32>>) -> List<&2, U32>:
  match encoded:
    case None{}: [2]
    case Some{bytes}: Con{1, bytes}

def initialize_checked(accepted: Bool, seed: Unit -> D.State) -> List<&2, U32>:
  match accepted:
    case False{}: [2]
    case True{}: initial_packet(P.encode(D.state_value(seed(Unit{}))))

def initialize(c: S.Configuration, identity: String, seed: Unit -> D.State) -> List<&2, U32>:
  initialize_checked(is_valid(c, identity), seed)

# Recovery checks the frozen configuration without reopening the private seed.
def recovery_packet(accepted: Bool) -> List<&2, U32>:
  match accepted:
    case False{}: [2]
    case True{}: [1]

def recover(c: S.Configuration, identity: String) -> List<&2, U32>:
  recovery_packet(is_valid(c, identity))
