import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Free.bend as Free
import ./Logic.bend as L
import ./ReadOnly.bend as RO
import ./Termination.bend as T
import ./Client.bend as Client
import ./Configuration.bend as C
import ./Instance.bend as I
import ./Bindings.bend as B

def B.certificate(ctx, args, s, valid, identity, n):
  Free.execution_trace_free_covers_prefixes_and_final(
    S.execute(n, Client.program(), C.schema(), s, ctx, args),
    C.schema(), C.limits(), S.environment(I.config()), s, ctx, B.code(), args)

def response_readonly(args: D.Value, r: S.Return) -> RO.Action(1n, Client.respond(args, r)):
  match r:
    case S.UnitValue{}: Unit{}
    case S.Datum{obs}:
      match obs:
        case D.Cell{v}: Unit{}
        case D.RowAbsent{}: Unit{}
        case D.Existence{b}: Unit{}
        case D.Count{n}: Unit{}
        case D.Keys{xs}: Unit{}

def read_only(ctx: D.Context, args: D.Value) -> RO.Action(2n, S.start(Client.program(), ctx, args)):
  match ctx:
    case D.Context{id, kind}: L.Both{Unit{}, r => response_readonly(args, r)}

def B.read_only(ctx, args):
  (2n, read_only(ctx, args))

def response_finite(args: D.Value, r: S.Return) -> T.Finite(1n, Client.respond(args, r)):
  match r:
    case S.UnitValue{}: Unit{}
    case S.Datum{obs}:
      match obs:
        case D.Cell{v}: Unit{}
        case D.RowAbsent{}: Unit{}
        case D.Existence{b}: Unit{}
        case D.Count{n}: Unit{}
        case D.Keys{xs}: Unit{}

def finite(ctx: D.Context, args: D.Value) -> T.Finite(2n, S.start(Client.program(), ctx, args)):
  match ctx:
    case D.Context{id, kind}: r => response_finite(args, r)

def B.terminates(s, ctx, args):
  +ctx = ctx
  +args = args
  T.program_finite(2n, Client.program(), C.schema(), s, ctx, args, finite(ctx, args))
