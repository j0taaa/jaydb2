# Reachable instance scenarios: seed + previous actual conclusions.
# Metatheory only; private data does not enter a submission's Book.
import Base
import ../contract/Data.bend as D
import ../contract/Interface.bend as I
import ../contract/Requirements.bend as R
import ../contract/Resources.bend as X
import ../contract/Semantics.bend as S
import ./HistoryService.bend as H

type Moment is Data:
  Initialization{}
  Service{reception: X.Reception}

def of_moment(~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, H.Record>, ~proof_initial: String,
  m: Moment, +world: Nat) -> I.Scenario:
  match m:
    case Initialization{}: I.Initialize{world, c, seed(Unit{}), proof_initial}
    case Service{r}: I.Serve{world, c, H.state(history(world), seed(Unit{})), r}

def canonical(~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, H.Record>, ~moment: Nat -> Moment,
  ~proof_initial: String, +world: Nat) -> I.Scenario:
  of_moment(c, seed, history, proof_initial, moment(world), world)

def StateOfCall(x: I.Scenario) -> Type:
  match x:
    case I.Initialize{m, c, s, pi}: Unit
    case I.Serve{m, c, s, r}: R.Valid(c, s)

def state_of_moment(~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, H.Record>, ~proof_initial: String,
  m: Moment, +world: Nat, initial: R.Valid(c, seed(Unit{})),
  sources: H.Sources(c, history(world), seed(Unit{}))) ->
  StateOfCall(of_moment(c, seed, history, proof_initial, m, world)):
  match m:
    case Initialization{}: Unit{}
    case Service{r}:
      H.history_preserves_validity(c, history(world), seed(Unit{}), initial, sources)

# The only supplied validity is the seed's; published validity follows by induction.
law state_of_each_call_and_valid:
  for ~c: S.Configuration
  for ~seed: Unit -> D.State
  for ~history: Nat -> List<&2, H.Record>
  for ~moment: Nat -> Moment
  for ~proof_initial: String
  for +world: Nat
  for initial: R.Valid(c, seed(Unit{}))
  for sources: H.Sources(c, history(world), seed(Unit{}))
  StateOfCall(canonical(c, seed, history, moment, proof_initial, world))
def state_of_each_call_and_valid(c, seed, history, moment, proof_initial, world, initial, sources):
  state_of_moment(c, seed, history, proof_initial, moment(world), world, initial, sources)
