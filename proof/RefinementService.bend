# Reopens guards of the same observer; grants no database laws.
import Base
import ../contract/Interface.bend as I
import ../contract/Logic.bend as L

# Guards belong to observation; E<Refl,P> = P is not assumed.
def observation_stored(-G: Type, -H: Type, -ob: Nat -> I.Fact -> Type,
  t: Nat, f: I.Fact) -> Type:
  L.E<G, L.E<H, ob(t, f)>>

def remove_guards(-G: Type, -H: Type, -P: Type, proof: L.E<G, L.E<H, P>>) -> P:
  match proof:
    case L.Both{g, L.Both{h, p}}: p

def combined_guards(-G: Type, -H: Type, -P: Type,
  guards: L.E<G, H>, proof: P) -> L.E<G, L.E<H, P>>:
  match guards:
    case L.Both{g, h}: L.Both{g, L.Both{h, proof}}
