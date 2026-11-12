# Bang is a scheduling annotation; source proofs retain the same semantics.
import Base
import ../../contract/Data.bend as D
import ../../contract/Semantics.bend as S
import ../../src/Termination.bend as T

# A small, genuinely used bang in the terminal value of both programs.
def mix(x: U32) -> U32:
  (x + 1 : U32)

def finish(x: U32) -> S.Action:
  S.Finish{D.VInt{0, mix!(x)}}

def read(key: String) -> S.Action:
  S.Access{D.ReadCell{D.Users{}, key, "credential"}, r => finish(7)}

def program() -> S.Program:
  S.Program{ctx => args => read("bob")}

# The real example's restricted-user law: even a failed read requires own ID.
def allowed(ctx: D.Context, op: D.Operation) -> Type:
  D.Context{id, kind} = ctx
  match op:
    case D.ReadCell{D.Users{}, key, column}: {key == id : String}
    case _: Empty

law bang_value:
  {finish(7) == S.Finish{D.VInt{0, 8}} : S.Action}
def bang_value(): {==}

law own_read:
  allowed(D.Context{"alice", "user"}, D.ReadCell{D.Users{}, "alice", "credential"})
def own_read(): {==}

law finite_read:
  T.Finite(2n, read("bob"))
def finite_read(): r => Unit{}

def all_allowed(+ctx: D.Context, ts: List<&2, S.OperationEvent>) -> Type:
  match ts:
    case Nil{}: Unit
    case Con{S.OperationEvent{op, effect}, rest}:
      # Local pair keeps this fixture independent of the example's relocation.
      Pair<allowed(ctx, op), all_allowed(ctx, rest)>

type Pair<-A: Type, -B: Type> is Type:
  Pair{left: A, right: B}

def accesses(h: S.Situation) -> Type:
  match h:
    case S.Stable{s}: Unit
    case S.Executing{s, ctx, code, args, w, ts}: all_allowed(ctx, ts)
    case S.Closed{s, ctx, code, args, w, ts, r}: all_allowed(ctx, ts)

def configuration() -> S.Configuration:
  S.Configuration{D.Schema{Nil{}}, S.MoreOneLaw{accesses, S.NoneLaw{}},
    S.Limits{32768n, 65536n, 32768n}, "gpu-negative-controls"}
