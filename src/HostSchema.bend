# Export the checked configuration's schema in the host store's canonical format.
import Base
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P

def kind_name(kind: D.ColumnKind) -> String:
  match kind:
    case D.TextValue{}: "TextValue"
    case D.Boolean{}: "Boolean"
    case D.Integer{}: "Integer"

def columns(cs: List<&2, D.Column>) -> D.Value:
  match cs:
    case Nil{}: D.VListEmpty{}
    case Con{D.Column{name, kind, optional}, rest}:
      D.VList{D.fields_value([D.Field{"kind", D.VText{kind_name(kind)}},
        D.Field{"name", D.VText{name}}, D.Field{"optional", D.VBool{optional}}]), columns(rest)}

def tables(ts: List<&2, D.SchemaTable>) -> D.Value:
  match ts:
    case Nil{}: D.VListEmpty{}
    case Con{D.SchemaTable{name, key, cs}, rest}:
      D.VList{D.fields_value([D.Field{"columns", columns(cs)}, D.Field{"key", D.VText{key}},
        D.Field{"name", D.VText{name}}]), tables(rest)}

def encoded(result: Maybe<&2, List<&2, U32>>) -> List<&2, U32>:
  match result:
    case Some{bytes}: bytes
    case None{}: Nil{}

def encode(schema: D.Schema) -> List<&2, U32>:
  D.Schema{ts} = schema
  encoded(P.encode(D.fields_value([D.Field{"tables", tables(ts)}])))
