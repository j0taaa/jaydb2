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

def done(args: D.Value, r: S.Return) -> RO.Action(1n, Client.finish(args, r)):
  match args:
    case D.VInt{hi, lo}: Unit{}
    case D.VBool{b}: Unit{}
    case _:
      match r:
        case S.Datum{D.Cell{v}}: Unit{}
        case _: Unit{}

def read_only(ctx: D.Context, args: D.Value) -> RO.Action(2n, S.start(Client.program(), ctx, args)):
  match ctx:
    case D.Context{id, kind}: L.Both{Unit{}, r => done(args, r)}

def B.read_only(ctx, args):
  (2n, read_only(ctx, args))

def finite(args: D.Value, r: S.Return) -> T.Finite(1n, Client.finish(args, r)):
  match args:
    case D.VInt{hi, lo}: Unit{}
    case D.VBool{b}: Unit{}
    case _:
      match r:
        case S.Datum{D.Cell{v}}: Unit{}
        case _: Unit{}

def program_finite(ctx: D.Context, args: D.Value) -> T.Finite(2n, S.start(Client.program(), ctx, args)):
  match ctx:
    case D.Context{id, kind}: r => finite(args, r)

def B.terminates(s, ctx, args):
  +ctx = ctx
  +args = args
  T.program_finite(2n, Client.program(), C.schema(), s, ctx, args, program_finite(ctx, args))
