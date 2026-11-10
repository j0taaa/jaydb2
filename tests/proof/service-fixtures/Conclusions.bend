# Nonempty ACTUAL complete serial histories, starting from the real boot
# registry (empty). No alternate preloaded registry or original cert is used.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Resources.bend as X
import ../../../contract/Semantics.bend as S
import ../../../proof/SourceService.bend as Source
import ../../../proof/ProtocolService.bend as Q
import ../../../proof/service/specification/ServiceLaws.bend as E
import ../../../proof/service/model/EventObserver.bend as O
import ../../../proof/service/model/FrameBounds.bend as B
import ../../../proof/service/model/serial/Decode.bend as Decode
import ../../../proof/service/model/serial/Dispatch.bend as Dispatch
import ../../../proof/service/model/serial/Engine.bend as Engine
import ../../../proof/service/model/serial/PreparationPrelude.bend as Prelude
import ../../../proof/service/laws/serial/header/History.bend as History
import ./Resolution.bend as Fixture

def seed(unit: Unit) -> D.State:
  E.database(Fixture.missing())

def script(+input: X.Reception) -> List<&2, Engine.Job>:
  [Engine.Job{input, Fixture.primitives(Dispatch.ArtifactPending{})}]

def malformed() -> X.Reception:
  X.BodyReceived{0, 3, [7, 3, 0]}

law a_real_cached_missing_entry_call_concludes_failure_in_its_complete_serial_history:
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  {B.query(O.Item, History.items(Fixture.configuration(), binding, public, script(Fixture.input()), seed, "fixture"),
    Prelude.phase_index(Decode.frames(Decode.run(Fixture.configuration(), E.database(Fixture.missing()), Fixture.input())), 3n)) ==
      Some{O.Item{1n, E.database(Fixture.missing()), Fixture.input(), O.Core{True{}, "", Q.Completed{S.response_error(S.Failure{}), E.database(Fixture.missing()), False{}}}}} : Maybe<&2, O.Item>}
def a_real_cached_missing_entry_call_concludes_failure_in_its_complete_serial_history(binding, public): {==}

law a_real_malformed_prepared_body_concludes_input_error_in_its_complete_serial_history:
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  {B.query(O.Item, History.items(Fixture.configuration(), binding, public, script(malformed()), seed, "fixture"),
    Prelude.phase_index(Decode.frames(Decode.run(Fixture.configuration(), E.database(Fixture.missing()), malformed())), 1n)) ==
      Some{O.Item{1n, E.database(Fixture.missing()), malformed(), O.Core{True{}, "", Q.Completed{S.response_error(S.Input{}), E.database(Fixture.missing()), False{}}}}} : Maybe<&2, O.Item>}
def a_real_malformed_prepared_body_concludes_input_error_in_its_complete_serial_history(binding, public): {==}
