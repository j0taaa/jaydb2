import Base
import ./Data.bend as D
import ./Requirements.bend as R
import ./Logic.bend as L
import ./Configuration.bend as C
def state() -> D.State:
  D.State{[D.Table{"amenities", []}, D.Table{"departments", []}, D.Table{"employees", []}, D.Table{"guests", []}, D.Table{"housekeeping_tasks", []}, D.Table{"maintenance_requests", []}, D.Table{"payments", []}, D.Table{"properties", []}, D.Table{"rate_plans", []}, D.Table{"reservation_amenities", []}, D.Table{"reservation_rates", []}, D.Table{"reservations", []}, D.Table{"reviews", []}, D.Table{"room_types", []}, D.Table{"rooms", []}], [D.Row{"bench", [
    D.Field{"credential", D.VText{"comparison-token"}},
    D.Field{"id", D.VText{"bench"}}, D.Field{"kind", D.VText{"user"}}]}]}
law initial_valid:
  R.Valid(C.config(), state())
def initial_valid():
  L.Both{{==}, Unit{}}
