import Base
import ../../../native/effects.bend as Native

type Configuration is Type:
  Config{memory: Nat, time: Nat}

def ignore(config: Configuration) -> U32:
  match config:
    case Config{memory, time}:
      1

def main() -> IO(Unit):
  do IO<Unit>:
    bytes : List<&2, U32> <- Native.read()
    Native.write([ignore(Config{536870912n, Nat.mul(120n, 1000000000n)})])
