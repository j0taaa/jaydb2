import Base
import ./Controller.bend as C
import ./Effects.bend as E

def main() -> IO(Unit):
  E.drive(C.State, C.step, C.Boot{})
