import Base
import ./Data.bend as D
import ./Semantics.bend as S

type Command is Data:
  ListTasks{}
  View{id: String}
  Save{id: String, title: String, completed: Bool, cancel: Bool}
  Remove{id: String}
  Conclude{id: String}
  Invalid{}

def combined_id(+action: String, +id: String) -> Command:
  Bool.pick(Command, String.eq(action, "view"), View{id},
    Bool.pick(Command, String.eq(action, "remove"), Remove{id},
      Bool.pick(Command, String.eq(action, "conclude"), Conclude{id}, Invalid{})))

def combined_task_cases(save: Bool, cancel: Bool, id: String, title: String, completed: Bool) -> Command:
  match save cancel:
    case True{} _: Save{id, title, completed, False{}}
    case False{} True{}: Save{id, title, completed, True{}}
    case False{} False{}: Invalid{}

def combined_task(+action: String, id: String, title: String, completed: Bool) -> Command:
  combined_task_cases(String.eq(action, "save"), String.eq(action, "cancel"), id, title, completed)

def analyze(args: D.Value) -> Command:
  match args:
    case D.VList{D.VText{action}, D.VListEmpty{}}:
      Bool.pick(Command, String.eq(action, "list"), ListTasks{}, Invalid{})
    case D.VList{D.VText{action}, D.VList{D.VText{id}, D.VListEmpty{}}}:
      combined_id(action, id)
    case D.VList{D.VText{action}, D.VList{D.VText{id}, D.VList{D.VText{title}, D.VList{D.VBool{done}, D.VListEmpty{}}}}}:
      combined_task(action, id, title, done)
    case _: Invalid{}

def fields(+owner: String, +id: String, title: String, done: Bool) -> List<&2, D.Field>:
  [D.Field{"completed", D.VBool{done}}, D.Field{"id", D.VText{id}},
    D.Field{"owner", D.VText{owner}}, D.Field{"title", D.VText{title}}]

def keys(xs: List<&2, String>) -> D.Value:
  match xs:
    case Nil{}: D.VListEmpty{}
    case Con{k, rest}: D.VList{D.VText{k}, keys(rest)}

def list_value(r: S.Return) -> D.Value:
  match r:
    case S.Datum{D.Keys{ks}}: keys(ks)
    case _: D.VAbsent{}

def listed(r: S.Return) -> S.Action:
  S.Finish{list_value(r)}

def detail_value(owner: String, id: String, title: String, r: S.Return) -> D.Value:
  match r:
    case S.Datum{D.Cell{D.VBool{done}}}:
      D.VRecord{"completed", D.VBool{done},
        D.VRecord{"id", D.VText{id}, D.VRecord{"owner", D.VText{owner},
          D.VRecord{"title", D.VText{title}, D.VRecordEmpty{}}}}}
    case _: D.VAbsent{}

def detail(owner: String, id: String, title: String, r: S.Return) -> S.Action:
  S.Finish{detail_value(owner, id, title, r)}

def text_received(r: S.Return) -> Maybe<&2, String>:
  match r:
    case S.Datum{D.Cell{D.VText{title}}}: Some{title}
    case _: None{}

def resume_title(+owner: String, +id: String, title: Maybe<&2, String>) -> S.Action:
  match title:
    case Some{text}:
      S.Access{D.ReadCell{D.Application{owner}, id, "completed"}, detail(owner, id, text)}
    case None{}: S.Finish{D.VAbsent{}}

def title_received(owner: String, id: String, r: S.Return) -> S.Action:
  resume_title(owner, id, text_received(r))

def conclude_title(+owner: String, +id: String, title: Maybe<&2, String>) -> S.Action:
  match title:
    case Some{text}:
      S.Access{D.DefineRow{D.Application{owner}, id, fields(owner, id, text, True{})},
        unit => S.Finish{D.VText{id}}}
    case None{}: S.Refuse{D.VText{"task not found"}}

def conclude_received(owner: String, id: String, r: S.Return) -> S.Action:
  conclude_title(owner, id, text_received(r))

def saved(cancel: Bool, id: String) -> S.Action:
  match cancel:
    case False{}: S.Finish{D.VText{id}}
    case True{}: S.Refuse{D.VText{"cancelled"}}

def command(+owner: String, p: Command) -> S.Action:
  match p:
    case ListTasks{}:
      S.Access{D.EnumerateKeys{D.Application{owner}}, listed}
    case View{+id}:
      S.Access{D.ReadCell{D.Application{owner}, id, "title"}, title_received(owner, id)}
    case Save{+id, title, done, cancel}:
      S.Access{D.DefineRow{D.Application{owner}, id, fields(owner, id, title, done)},
        unit => saved(cancel, id)}
    case Conclude{+id}:
      S.Access{D.ReadCell{D.Application{owner}, id, "title"}, conclude_received(owner, id)}
    case Remove{+id}:
      S.Access{D.RemoveRow{D.Application{owner}, id}, unit => S.Finish{D.VText{id}}}
    case Invalid{}: S.Refuse{D.VText{"invalid request"}}

def start(ctx: D.Context, args: D.Value) -> S.Action:
  D.Context{id, kind} = ctx
  command(id, analyze(args))

def program() -> S.Program:
  S.Program{start}
