import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Free.bend as F
import ./Termination.bend as T
import ./Client.bend as Client
import ./Configuration.bend as C
import ./Instance.bend as I
import ./Bindings.bend as B

def B.certificate(ctx, args, s, valid, identity, n):
  +context = ctx
  +arguments = args
  F.execution_trace_free_covers_prefixes_and_final(
    S.execute(n, Client.program(), C.schema(), s, context, arguments),
    C.schema(), C.limits(), S.environment(I.config()), s, context, B.code(), arguments)

def accepted_finite(n: Nat, k: U32 -> S.Action, low: U32,
  witness: @word: U32 -> T.Finite(1n+n, k(word)), valid: Bool) ->
  T.Finite(1n+n, Client.accepted(k, low, valid)):
  match valid:
    case False{}: Unit{}
    case True{}: witness(low)

def cell_finite(n: Nat, k: U32 -> S.Action,
  witness: @low: U32 -> T.Finite(1n+n, k(low)), v: D.Value) ->
  T.Finite(1n+n, Client.cell(k, v)):
  match v:
    case D.VInt{high, low}: accepted_finite(n, k, low, witness, U32.is_eq(high, 0))
    case D.VAbsent{}: Unit{}
    case D.VBool{b}: Unit{}
    case D.VText{txt}: Unit{}
    case D.VListEmpty{}: Unit{}
    case D.VList{h, t}: Unit{}
    case D.VRecordEmpty{}: Unit{}
    case D.VRecord{name, item, tail}: Unit{}

def observed_finite(n: Nat, k: U32 -> S.Action,
  witness: @low: U32 -> T.Finite(1n+n, k(low)), o: D.Observation) ->
  T.Finite(1n+n, Client.observed(k, o)):
  match o:
    case D.Cell{v}: cell_finite(n, k, witness, v)
    case D.RowAbsent{}: Unit{}
    case D.Existence{exists}: Unit{}
    case D.Count{count}: Unit{}
    case D.Keys{keys}: Unit{}

def value_finite(n: Nat, k: U32 -> S.Action,
  witness: @low: U32 -> T.Finite(1n+n, k(low)), r: S.Return) ->
  T.Finite(1n+n, Client.value(k, r)):
  match r:
    case S.Datum{o}: observed_finite(n, k, witness, o)
    case S.UnitValue{}: Unit{}

def read_finite(+n: Nat, key: String, k: U32 -> S.Action,
  witness: @low: U32 -> T.Finite(1n+n, k(low))) -> T.Finite(2n+n, Client.read(key, k)):
  r => value_finite(n, k, witness, r)

def moved_finite(from: String, to: String, +left: U32, +right: U32, blocked: Bool) ->
  T.Finite(3n, Client.moved(from, to, left, right, blocked)):
  match blocked:
    case False{}: r1 => r2 => Unit{}
    case True{}: Unit{}

def transfer_finite(+from: String, +to: String, same: Bool) ->
  T.Finite(5n, Client.transferred(from, to, same)):
  match same:
    case False{}:
      read_finite(3n, from, left => Client.read(to, right => Client.move_values(from, to, left, right)),
        +left => read_finite(2n, to, right => Client.move_values(from, to, left, right),
          +right => moved_finite(from, to, left, right,
            U32.is_eq(left, 0) || U32.is_eq(right, 4294967295))))
    case True{}: Unit{}

def increment_finite(key: String, +old: U32, overflow: Bool) ->
  T.Finite(4n, Client.increment_value(key, old, overflow)):
  match overflow:
    case False{}: r => Unit{}
    case True{}: Unit{}

def finite(c: Client.Command) -> T.Finite(5n, Client.execute(c)):
  match c:
    case Client.Read{key}: read_finite(3n, key, Client.show, low => Unit{})
    case Client.Increment{+key}:
      read_finite(3n, key, +old => Client.increment_value(key, old, U32.is_eq(old, 4294967295)),
        +old => increment_finite(key, old, U32.is_eq(old, 4294967295)))
    case Client.Transfer{+from, +to}: transfer_finite(from, to, String.eq(from, to))
    case Client.Invalid{}: Unit{}

def B.terminates(s, ctx, args):
  +arguments = args
  T.program_finite(5n, Client.program(), C.schema(), s, ctx, arguments,
    finite(Client.command(arguments)))
