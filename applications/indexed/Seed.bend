import Base
import ./Data.bend as D
import ./Logic.bend as L
import ./Requirements.bend as R
import ./Model.bend as M
import ./Configuration.bend as C

def state() -> D.State:
  M.state(False{},False{})

law initial_valid:
  R.Valid(C.config(),state())
def initial_valid():
  L.Both{{==},L.Both{M.Laid{False{},False{},[M.entry(False{})],[M.entry(False{})],{==}},L.Both{L.Both{{==},{==}},Unit{}}}}
