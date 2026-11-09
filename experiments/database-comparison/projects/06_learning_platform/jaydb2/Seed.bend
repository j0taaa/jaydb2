import Base
import ./Data.bend as D
import ./Requirements.bend as R
import ./Logic.bend as L
import ./Configuration.bend as C
def state() -> D.State:
  D.State{[D.Table{"assignments", []}, D.Table{"cohorts", []}, D.Table{"courses", []}, D.Table{"enrollments", []}, D.Table{"grades", []}, D.Table{"instructors", []}, D.Table{"learners", []}, D.Table{"lessons", []}, D.Table{"modules", []}, D.Table{"organizations", []}, D.Table{"payments", []}, D.Table{"submissions", []}], [D.Row{"bench", [
    D.Field{"credential", D.VText{"comparison-token"}},
    D.Field{"id", D.VText{"bench"}}, D.Field{"kind", D.VText{"user"}}]}]}
law initial_valid:
  R.Valid(C.config(), state())
def initial_valid():
  L.Both{{==}, Unit{}}
