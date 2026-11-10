# Semantic call-world projection and positivity, shared independently of
# interleaving clocks or legacy law transport. Definitions moved unchanged.
import Base
import ../../../contract/Logic.bend as L
import ./EventObserver.bend as O

def world(item: O.Item) -> Nat:
  O.Item{world, selected, input, event} = item
  world


def CallWorld(world: Nat) -> Type:
  match world:
    case 0n: Empty
    case 1n+previous: Unit


def AllCallWorlds(items: List<&2, O.Item>) -> Type:
  match items:
    case Nil{}: Unit
    case Con{item, rest}: L.E<CallWorld(world(item)), AllCallWorlds(rest)>
