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

def selected_readonly(keys: Bool, table: String, key: String, column: String) ->
  RO.Operation(Client.selected(keys, table, key, column)):
  match keys:
    case True{}: Unit{}
    case False{}: Unit{}

def read_only(ctx: D.Context, +args: D.Value) ->
  RO.Action(2n, S.start(Client.program(), ctx, args)):
  L.Both{selected_readonly(String.eq(Client.text(Client.arg(args, 0n)), "keys"),
    Client.text(Client.arg(args, 1n)), Client.text(Client.arg(args, 2n)),
    Client.text(Client.arg(args, 3n))), r => Unit{}}

def B.read_only(ctx, args):
  (2n, read_only(ctx, args))

def finite(ctx: D.Context, args: D.Value) ->
  T.Finite(2n, S.start(Client.program(), ctx, args)):
  r => Unit{}

def B.terminates(s, ctx, args):
  +ctx = ctx
  +args = args
  T.program_finite(2n, Client.program(), C.schema(), s, ctx, args, finite(ctx, args))
