# Instantiates the protocol with reachable scenarios of the same configuration.
# Other fields are independent tool and environment contracts.
import Base
import ../contract/Data.bend as D
import ../contract/Interface.bend as I
import ../contract/Semantics.bend as S
import ./SourceService.bend as F
import ./ScenariosService.bend as C
import ./HistoryService.bend as H

def combined_scenarios(base: F.Source, scenarios: Nat -> I.Scenario) -> F.Source:
  match base:
    case F.Source{id, k, previous, initial, calls, program, elaborates, derives, processable, failure, delivery}:
      F.Source{id, k, scenarios, initial, calls, program, elaborates, derives, processable, failure, delivery}

def source(~base: F.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, H.Record>, ~moment: Nat -> C.Moment,
  ~proof_initial: String) -> F.Source:
  combined_scenarios(base, world => C.canonical(c, seed, history, moment, proof_initial, world))

def query_substituted(base: F.Source, -scenarios: Nat -> I.Scenario, -world: Nat) ->
  {F.scenario(combined_scenarios(base, scenarios), world) == scenarios(world) : I.Scenario}:
  match base:
    case F.Source{id, k, cs, ins, hs, ps, el, de, pr, fr, ef}: {==}

law scenario_of_model:
  for ~base: F.Source
  for ~c: S.Configuration
  for ~seed: Unit -> D.State
  for ~history: Nat -> List<&2, H.Record>
  for ~moment: Nat -> C.Moment
  for ~proof_initial: String
  for -world: Nat
  {F.scenario(source(base, c, seed, history, moment, proof_initial), world) ==
    C.canonical(c, seed, history, moment, proof_initial, world) : I.Scenario}
def scenario_of_model(base, c, seed, history, moment, proof_initial, world):
  query_substituted(base, m => C.canonical(c, seed, history, moment, proof_initial, m), world)
