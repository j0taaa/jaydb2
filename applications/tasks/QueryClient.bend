# Optional task flow over caller-supplied keys, not a second task runtime.
import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Query.bend as Q
import ./Action.bend as A
import ./Task.bend as Task
import ./Mutation.bend as M
import ./ReadProgram.bend as RP

type Command is Data:
  Open{first: String, second: String}
  Pair{first: String, second: String, cancel: Bool}
  Inspect{key: String}
  Insert{key: String}
  Replace{key: String}
  Cas{key: String, expected: Bool}
  Drop{first: String, second: String}
  Invalid{}

def analyze(args: D.Value) -> Command:
  match args:
    case D.VList{D.VText{"open"}, D.VList{D.VText{a}, D.VList{D.VText{b}, D.VListEmpty{}}}}:
      Open{a, b}
    case D.VList{D.VText{"pair"}, D.VList{D.VText{a}, D.VList{D.VText{b}, D.VList{D.VBool{cancel}, D.VListEmpty{}}}}}:
      Pair{a, b, cancel}
    case D.VList{D.VText{"insert"}, D.VList{D.VText{key}, D.VListEmpty{}}}: Insert{key}
    case D.VList{D.VText{"replace_open"}, D.VList{D.VText{key}, D.VListEmpty{}}}: Replace{key}
    case D.VList{D.VText{"drop"}, D.VList{D.VText{a}, D.VList{D.VText{b}, D.VListEmpty{}}}}: Drop{a, b}
    case D.VList{D.VText{"cas"}, D.VList{D.VText{key}, D.VList{D.VBool{expected}, D.VListEmpty{}}}}: Cas{key, expected}
    case D.VList{D.VText{"inspect"}, D.VList{D.VText{key}, D.VListEmpty{}}}: Inspect{key}
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

def is_open(obs: D.Observation) -> Bool:
  match obs:
    case D.Cell{D.VBool{False{}}}: True{}
    case _: False{}

def command(+owner: String, p: Command) -> S.Action:
  match p:
    case Open{a, b}:
      Q.filter_map(~String, ~visit, owner, [a, b], value => S.Finish{value})
    case Pair{+a, +b, cancel}:
      A.define_rows(D.Application{owner},
        [D.Row{a, Task.fields(owner, a, "First", False{})},
         D.Row{b, Task.fields(owner, b, "Second", True{})}], Task.saved(cancel, a))
    case Inspect{key}: RP.select(D.Application{owner}, key, ["completed", "title"])
    case Insert{+key}: M.insert_if_absent(D.Application{owner}, D.Row{key, Task.fields(owner, key, "Once", False{})}, b => S.Finish{D.VBool{b}})
    case Replace{+key}: M.replace_if(~is_open, D.Application{owner}, D.Row{key, Task.fields(owner, key, "Replaced", True{})}, "completed", b => S.Finish{D.VBool{b}})
    case Cas{+key, expected}: M.compare_exchange(D.Application{owner}, D.Row{key, Task.fields(owner, key, "Replaced", True{})}, "completed", D.VBool{expected}, b => S.Finish{D.VBool{b}})
    case Drop{a, b}: M.remove_rows(D.Application{owner}, [a, b], S.Finish{D.VAbsent{}})
    case Invalid{}: S.Refuse{D.VText{"invalid query request"}}

def start(ctx: D.Context, args: D.Value) -> S.Action:
  command(D.context_id(ctx), analyze(args))

def program() -> S.Program:
  S.Program{start}
