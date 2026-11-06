import Base
import ./Data.bend as D
import ./Requirements.bend as R
import ./Logic.bend as L
import ./Configuration.bend as C
def state() -> D.State:
  D.State{[D.Table{"appointments", []}, D.Table{"clinicians", []}, D.Table{"diagnoses", []}, D.Table{"encounter_diagnoses", []}, D.Table{"encounters", []}, D.Table{"invoices", []}, D.Table{"patients", []}, D.Table{"prescriptions", []}, D.Table{"rooms", []}, D.Table{"specialties", []}], [D.Row{"bench", [
    D.Field{"credential", D.VText{"comparison-token"}},
    D.Field{"id", D.VText{"bench"}}, D.Field{"kind", D.VText{"user"}}]}]}
law initial_valid:
  R.Valid(C.config(), state())
def initial_valid():
  L.Both{{==}, Unit{}}
