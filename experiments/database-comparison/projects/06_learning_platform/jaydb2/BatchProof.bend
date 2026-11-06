import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Free.bend as L
import ./Termination.bend as T
import ./Client.bend as Client
import ./Configuration.bend as C
import ./Instance.bend as I
import ./Bindings.bend as B
def B.certificate(ctx, args, s, valid, identity, n):
  L.execution_trace_free_covers_prefixes_and_final(
    S.execute(n, Client.program(), C.schema(), s, ctx, args),
    C.schema(), C.limits(), S.environment(I.config()), s, ctx, B.code(), args)
def finite(ctx: D.Context, args: D.Value) ->
  T.Finite(3n, S.start(Client.program(), ctx, args)):
  r0 => r1 => Unit{}
def B.terminates(s, ctx, args):
  +context = ctx
  +arguments = args
  T.program_finite(3n, Client.program(), C.schema(), s, context, arguments,
    finite(context, arguments))
