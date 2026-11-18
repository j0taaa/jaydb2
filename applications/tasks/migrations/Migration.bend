import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Requirements.bend as R
import ./Logic.bend as L
import ./Old/Configuration.bend as Old
import ./Old/Policy.bend as OldPolicy
import ./Configuration.bend as New
import ./Policy.bend as NewPolicy

# In the old schema, every task has completed, id, owner, then title.
def add_priority(fs: List<&2, D.Field>) -> List<&2, D.Field>:
  match fs:
    case Con{a, Con{b, Con{c, rest}}}:
      Con{a, Con{b, Con{c, Con{D.Field{"priority", D.VAbsent{}}, rest}}}}
    case other: other

def rows(ls: List<&2, D.Row>) -> List<&2, D.Row>:
  match ls:
    case Nil{}: Nil{}
    case Con{D.Row{key, fs}, rest}:
      Con{D.Row{key, add_priority(fs)}, rows(rest)}

def tables(ts: List<&2, D.Table>) -> List<&2, D.Table>:
  match ts:
    case Nil{}: Nil{}
    case Con{D.Table{name, ls}, rest}:
      Con{D.Table{name, rows(ls)}, tables(rest)}

def migrate(s: D.State) -> D.State:
  D.State{ts, us} = s
  D.State{tables(ts), us}

law same_owner:
  for fs: List<&2, D.Field>
  {D.find_field(add_priority(fs), "owner") == D.find_field(fs, "owner") : Maybe<&2, D.Value>}
def same_owner(fs):
  match fs:
    case Nil{}: {==}
    case Con{a, Nil{}}: {==}
    case Con{a, Con{b, Nil{}}}: {==}
    case Con{D.Field{a, av}, Con{D.Field{b, bv}, Con{D.Field{c, cv}, rest}}}: {==}

def preserve_rows(+us: List<&2, D.Row>, +name: String, ls: List<&2, D.Row>,
  h: OldPolicy.Rows(us, name, ls)) -> NewPolicy.Rows(us, name, rows(ls)):
  match ls:
    case Nil{}: Unit{}
    case Con{D.Row{key, +fs}, rest}:
      OldPolicy.Both{OldPolicy.Both{owner, user}, tail} = h
      NewPolicy.Both{NewPolicy.Both{
        Equal.trans(Maybe<&2, D.Value>, D.find_field(add_priority(fs), "owner"),
          D.find_field(fs, "owner"), Some{D.VText{name}}, same_owner(fs), owner), user},
        preserve_rows(us, name, rest, tail)}

def preserve_tables(+us: List<&2, D.Row>, ts: List<&2, D.Table>,
  h: OldPolicy.Tables(us, ts)) -> NewPolicy.Tables(us, tables(ts)):
  match ts:
    case Nil{}: Unit{}
    case Con{D.Table{name, ls}, rest}:
      OldPolicy.Both{owners, tail} = h
      NewPolicy.Both{preserve_rows(us, name, ls, owners), preserve_tables(us, rest, tail)}

law preserves:
  for +s: D.State
  for valid: R.Valid(Old.config(), s)
  S.Satisfies(New.config(), S.Stable{migrate(s)})
def preserves(s, valid):
  D.State{ts, +us} = s
  L.Both{structure, L.Both{owners, rest}} = valid
  L.Both{preserve_tables(us, ts, owners), Unit{}}
