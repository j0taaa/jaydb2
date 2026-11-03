import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Free.bend as L
import ./Termination.bend as T
import ./Client.bend as Client
import ./Configuration.bend as C
import ./Instance.bend as I
import ./Bindings.bend as B

def B.certificate(s, valid, identity, n):
  L.execution_trace_free_covers_prefixes_and_final(
    S.execute(n, Client.program(), C.schema(), s, I.context(), I.arguments()),
    C.schema(), C.limits(), S.environment(I.config()), s, I.context(), B.code(), I.arguments())

def finite(ctx: D.Context, args: D.Value) ->
  T.Finite(1n, S.start(Client.program(), ctx, args)):
  match ctx:
    case D.Context{id, kind}:
      Unit{}

def B.terminates(s, ctx, args):
  +context = ctx
  +arguments = args
  T.program_finite(1n, Client.program(), C.schema(), s, context, arguments,
    finite(context, arguments))
