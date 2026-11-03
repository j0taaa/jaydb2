# Optional task flow over caller-supplied keys, not a second task runtime.
import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Query.bend as Q
import ./Action.bend as A
import ./Task.bend as Task

type Command is Data:
  Open{first: String, second: String}
  Pair{first: String, second: String, cancel: Bool}
  Invalid{}

def analyze(args: D.Value) -> Command:
  match args:
    case D.VList{D.VText{"open"}, D.VList{D.VText{a}, D.VList{D.VText{b}, D.VListEmpty{}}}}:
      Open{a, b}
    case D.VList{D.VText{"pair"}, D.VList{D.VText{a}, D.VList{D.VText{b}, D.VList{D.VBool{cancel}, D.VListEmpty{}}}}}:
      Pair{a, b, cancel}
    case _: Invalid{}

type Projection is Data:
  Keep{value: D.Value}
  Skip{}
  InvalidProjection{}

def projection(result: Q.Selection) -> Projection:
  match result:
    case Q.Selected{D.VRecord{"completed", D.VBool{False{}}, D.VRecord{"title", D.VText{title}, D.VRecordEmpty{}}}}:
      Keep{D.VRecord{"title", D.VText{title}, D.VRecordEmpty{}}}
    case Q.Selected{D.VRecord{"completed", D.VBool{True{}}, D.VRecord{"title", D.VText{title}, D.VRecordEmpty{}}}}:
      Skip{}
    case Q.MissingRow{}: Skip{}
    case _: InvalidProjection{}

def finish_projection(done: Maybe<&2, D.Value> -> S.Action, p: Projection) -> S.Action:
  match p:
    case Keep{value}: done(Some{value})
    case Skip{}: done(None{})
    case InvalidProjection{}: S.Refuse{D.VText{"unexpected task fields"}}

def projected(done: Maybe<&2, D.Value> -> S.Action, result: Q.Selection) -> S.Action:
  finish_projection(done, projection(result))

def visit(owner: String, key: String, done: Maybe<&2, D.Value> -> S.Action) -> S.Action:
  Q.select(D.Application{owner}, key, ["completed", "title"], projected(done))

def command(+owner: String, p: Command) -> S.Action:
  match p:
    case Open{a, b}:
      Q.filter_map(~String, ~visit, owner, [a, b], value => S.Finish{value})
    case Pair{+a, +b, cancel}:
      A.define_rows(D.Application{owner},
        [D.Row{a, Task.fields(owner, a, "First", False{})},
         D.Row{b, Task.fields(owner, b, "Second", True{})}], Task.saved(cancel, a))
    case Invalid{}: S.Refuse{D.VText{"invalid query request"}}

def start(ctx: D.Context, args: D.Value) -> S.Action:
  command(D.context_id(ctx), analyze(args))

def program() -> S.Program:
  S.Program{start}
