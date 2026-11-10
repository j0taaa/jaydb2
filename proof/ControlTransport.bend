# Logical registry values survive the private adapter without losing fields.
import Base
import ../contract/Data.bend as D
import ../contract/PreparedRegistry.bend as G
import ../src/Control.bend as C
import ../src/ControlBridge.bend as Wire

law strings_roundtrip:
  for xs: List<&2, String>
  {Wire.read_strings(Wire.strings(xs)) == Some{xs} : Maybe<&2, List<&2, String>>}
def strings_roundtrip(xs):
  match xs:
    case Nil{}: {==}
    case Con{+h, +rest}:
      Equal.cong(Maybe<&2, List<&2, String>>, Maybe<&2, List<&2, String>>,
        tail => Wire.cons_string(h, tail), Wire.read_strings(Wire.strings(rest)), Some{rest}, strings_roundtrip(rest))

law entries_roundtrip:
  for es: List<&2, G.Entry>
  {Wire.read_entries(Wire.entries(es)) == Some{es} : Maybe<&2, List<&2, G.Entry>>}
def entries_roundtrip(es):
  match es:
    case Nil{}: {==}
    case Con{G.Entry{i, h, code, proof, ro, seal}, +rest}:
      Equal.cong(Maybe<&2, List<&2, G.Entry>>, Maybe<&2, List<&2, G.Entry>>,
        tail => Wire.cons_entry(Wire.entry(G.Entry{i, h, code, proof, ro, seal}), tail),
        Wire.read_entries(Wire.entries(rest)), Some{rest}, entries_roundtrip(rest))

law registry_roundtrip:
  for reg: C.Registry
  {Wire.read_registry(Wire.registry(reg)) == Some{reg} : Maybe<&2, C.Registry>}
def registry_roundtrip(reg):
  match reg:
    case C.ControlRegistry{+es, +history}:
      %Equal.sym(Maybe<&2, List<&2, G.Entry>>, Wire.read_entries(Wire.entries(es)), Some{es}, entries_roundtrip(es)) :
        {Wire.read_registry_parts(_, Wire.read_strings(Wire.strings(history))) == Some{C.ControlRegistry{es, history}} : Maybe<&2, C.Registry>}
      Equal.cong(Maybe<&2, List<&2, String>>, Maybe<&2, C.Registry>,
        used => Wire.read_registry_parts(Some{es}, used),
        Wire.read_strings(Wire.strings(history)), Some{history}, strings_roundtrip(history))
