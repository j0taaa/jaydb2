# Ordinary tables only: schema id:text, target:text, value:text (all required).
# Applications supply laws for consistency AND permission for EVERY access.
import Base
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ./Key.bend as K
import ./Query.bend as Q
import ./Read.bend as R
import ./Mutation.bend as M
import ./Action.bend as A

def append(xs: List<&2, String>, ys: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}: ys
    case Con{x, rest}: Con{x, append(rest, ys)}

def entry(+key: String, parts: List<&2, String>, target: String) -> D.Row:
  D.Row{key, [D.Field{"id", D.VText{key}}, D.Field{"target", D.VText{target}}, D.Field{"value", D.VText{K.encode(parts)}}]}

def unique(+parts: List<&2, String>, target: String) -> D.Row:
  entry(K.encode(parts), parts, target)

def nonunique(+parts: List<&2, String>, +target: String) -> D.Row:
  entry(K.encode(append(parts, [target])), parts, target)

# False means occupied, including repeated claims by the same target.
def claim(c: D.Collection, parts: List<&2, String>, target: String, done: Bool -> S.Action) -> S.Action:
  M.insert_if_absent(c, unique(parts, target), done)

def lookup(c: D.Collection, parts: List<&2, String>, done: Q.Selection -> S.Action) -> S.Action:
  Q.select(c, K.encode(parts), ["target"], done)

def selected(+value: String, done: Maybe<&2, D.Value> -> S.Action, result: Q.Selection) -> S.Action:
  match result:
    case Q.Selected{D.VRecord{"target", D.VText{target}, D.VRecord{"value", D.VText{v}, D.VRecordEmpty{}}}}:
      done(Bool.pick(Maybe<&2, D.Value>, String.eq(value, v), Some{D.VText{target}}, None{}))
    case Q.MissingRow{}: done(None{})
    case _: S.Refuse{D.VText{"invalid index entry"}}

type Scan is Data:
  Scan{collection: D.Collection, value: String}

def visit(env: Scan, key: String, done: Maybe<&2, D.Value> -> S.Action) -> S.Action:
  Scan{c, value} = env
  Q.select(c, key, ["target", "value"], selected(value, done))

# Equality scan over an ordinary nonunique/composite index. All keys and both
# cells of every entry are accessed, including entries filtered out.
def lookup_many(+c: D.Collection, parts: List<&2, String>, done: D.Value -> S.Action) -> S.Action:
  R.keys(c, keys => Q.filter_map(~Scan, ~visit, Scan{c, K.encode(parts)}, keys, done))

# Explicit destructive rebuild in this SAME transaction; no auto triggers.
def rebuild(+c: D.Collection, rows: List<&2, D.Row>, done: S.Action) -> S.Action:
  R.keys(c, keys => M.remove_rows(c, keys, A.define_rows(c, rows, done)))

# Maintenance helper: caller supplies old entry keys and complete new entries.
# The final law must require that these correspond to the business mutation.
def maintain(+c: D.Collection, old: List<&2, String>, rows: List<&2, D.Row>, business: S.Action) -> S.Action:
  M.remove_rows(c, old, A.define_rows(c, rows, business))
