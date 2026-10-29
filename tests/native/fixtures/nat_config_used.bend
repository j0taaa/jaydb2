import Base
import ../../../native/effects.bend as Native

type Configuration is Type:
  Config{memory: Nat, time: Nat}

def positive(memory: Nat, time: Nat) -> U32:
  match memory time:
    case 0n t:
      0
    case m 0n:
      0
    case 1n+m 1n+t:
      1

def validate(config: Configuration) -> U32:
  match config:
    case Config{memory, time}:
      positive(memory, time)

def main() -> IO(Unit):
  do IO<Unit>:
    bytes : List<&2, U32> <- Native.read()
    Native.write([validate(Config{536870912n, Nat.mul(120n, 1000000000n)})])
