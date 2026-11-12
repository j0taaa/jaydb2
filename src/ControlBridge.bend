# Exact private serialization for the checked control executable. The host
# forwards the latest registry bytes unchanged (T3). Public receipts come
# from Control.
import Base
import ./LimitWords.bend as LimitWords
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/PreparedRegistry.bend as G
import ../contract/Semantics.bend as S
import ../contract/Requirements.bend as R
import ./Control.bend as C
import ./Codec.bend as Codec
import ./State.bend as State
import ./Messages.bend as M
import ./Transport.bend as T

def strings(xs: List<&2, String>) -> D.Value:
  match xs:
    case Nil{}: D.VListEmpty{}
    case Con{x, rest}: D.VList{D.VText{x}, strings(rest)}

def entry(e: G.Entry) -> D.Value:
  G.Entry{i, h, c, p, ro, seal} = e
  D.VList{D.VText{i}, D.VList{D.VText{h}, D.VList{D.VText{c}, D.VList{D.VText{p},
    D.VList{D.VBool{ro}, D.VList{D.VText{seal}, D.VListEmpty{}}}}}}}

def entries(es: List<&2, G.Entry>) -> D.Value:
  match es:
    case Nil{}: D.VListEmpty{}
    case Con{e, rest}: D.VList{entry(e), entries(rest)}

def registry(r: C.Registry) -> D.Value:
  C.ControlRegistry{es, used} = r
  D.VList{entries(es), D.VList{strings(used), D.VListEmpty{}}}

def cons_string(h: String, t: Maybe<&2, List<&2, String>>) -> Maybe<&2, List<&2, String>>:
  match t:
    case None{}: None{}
    case Some{rest}: Some{Con{h, rest}}

def read_strings(v: D.Value) -> Maybe<&2, List<&2, String>>:
  match v:
    case D.VListEmpty{}: Some{Nil{}}
    case D.VList{D.VText{h}, rest}: cons_string(h, read_strings(rest))
    case _: None{}

def cons_entry(e: D.Value, t: Maybe<&2, List<&2, G.Entry>>) -> Maybe<&2, List<&2, G.Entry>>:
  match e t:
    case D.VList{D.VText{i}, D.VList{D.VText{h}, D.VList{D.VText{c}, D.VList{D.VText{p}, D.VList{D.VBool{ro}, D.VList{D.VText{seal}, D.VListEmpty{}}}}}}} Some{rest}:
      Some{Con{G.Entry{i, h, c, p, ro, seal}, rest}}
    case _ _: None{}

def read_entries(v: D.Value) -> Maybe<&2, List<&2, G.Entry>>:
  match v:
    case D.VListEmpty{}: Some{Nil{}}
    case D.VList{h, rest}: cons_entry(h, read_entries(rest))
    case _: None{}

def read_registry_parts(es: Maybe<&2, List<&2, G.Entry>>, used: Maybe<&2, List<&2, String>>) -> Maybe<&2, C.Registry>:
  match es used:
    case Some{entries} Some{history}: Some{C.ControlRegistry{entries, history}}
    case _ _: None{}

def read_registry(v: D.Value) -> Maybe<&2, C.Registry>:
  match v:
    case D.VList{es, D.VList{used, D.VListEmpty{}}}: read_registry_parts(read_entries(es), read_strings(used))
    case _: None{}

# The universal mode tag is a T1 result from admission, supplied privately.
# Exact admitted code/proof are compared by Control to the original body.
def admission(ok: Bool, i: String, code: String, proof: String) -> C.Admission:
  match ok:
    case True{}: C.ControlUniversal{i, code, proof}
    case False{}: C.ControlUnaccepted{}

def delta(change: C.Change) -> List<&2, U32>:
  match change:
    case C.ControlAdd{G.Entry{i, h, c, p, ro, seal}}: B.utf8(h)
    case C.ControlRemove{i, h}: B.utf8(h)

# Private result: 0||denial; 1||frame(handle)||frame(registry)||receipt (add),
# 3||frame(handle)||frame(registry)||receipt (remove). No database publication.
def join_encoded(encoded: Maybe<&2, List<&2, U32>>, rest: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match encoded:
    case None{}: None{}
    case Some{bs}: T.join(bs, rest)

def ready(tag: U32, handle: List<&2, U32>, next: C.Registry, receipt: List<&2, U32>) -> List<&2, U32>:
  M.prefix(tag, M.join(handle, join_encoded(P.encode(registry(next)), receipt)))


def output_ready(+change: C.Change, next: C.Registry, bytes: List<&2, U32>) -> List<&2, U32>:
  match change:
    case C.ControlAdd{e}: ready(1, delta(C.ControlAdd{e}), next, bytes)
    case C.ControlRemove{i, h}: ready(3, B.utf8(h), next, bytes)

def output(result: C.Transition) -> List<&2, U32>:
  match result:
    case C.ControlResult{root, last, registry, C.ControlTransaction{response}}:
      M.prefix(0, P.frame(S.response_value(response)))
    case C.ControlResult{root, last, registry, C.ControlMetadata{receipt, bytes, change}}:
      output_ready(change, registry, bytes)

def decoded_registry(value: Codec.Outcome) -> Maybe<&2, C.Registry>:
  match value:
    case Codec.Decoded{v}: read_registry(v)
    case _: None{}

def decode_registry(bytes: List<&2, U32>) -> Maybe<&2, C.Registry>:
  match bytes:
    case Nil{}: Some{C.ControlRegistry{Nil{}, Nil{}}}
    case bs: decoded_registry(Codec.decode(bs, B.Number64{4294967295, 4294967295}))

def run(~c: S.Configuration, root: Maybe<&2, D.State>, registry: Maybe<&2, C.Registry>,
  metadata: Codec.Outcome, body: List<&2, U32>) -> List<&2, U32>:
  match root registry metadata:
    case Some{s} Some{reg} Codec.Decoded{D.VText{code}}:
      output(C.host_error(code, s, Nil{}, reg))
    case Some{s} Some{+reg} Codec.Decoded{D.VList{D.VText{h}, D.VList{D.VText{mode}, D.VList{D.VText{code}, D.VList{D.VText{proof}, D.VListEmpty{}}}}}}:
      output(C.control(c, s, Nil{}, reg, body, admission(String.eq(mode, "universal"), S.environment(c), code, proof), h))
    case _ _ _: [2]

def root_value(~c: S.Configuration, decoded: Codec.Outcome, registry: Maybe<&2, C.Registry>,
  metadata: Codec.Outcome, body: List<&2, U32>) -> List<&2, U32>:
  match decoded:
    case Codec.Decoded{v}: run(c, State.decode(v, S.schema(c)), registry, metadata, body)
    case _: [2]

def root_limit(~c: S.Configuration, limit: Maybe<&2, B.Number64>, state: List<&2, U32>,
  registry: Maybe<&2, C.Registry>, metadata: Codec.Outcome, body: List<&2, U32>) -> List<&2, U32>:
  match limit:
    case None{}: [2]
    case Some{n}: root_value(c, Codec.decode(state, n), registry, metadata, body)

def root_parts(~c: S.Configuration, parts: Maybe<&2, T.Parts>, registry: Maybe<&2, C.Registry>,
  metadata: Codec.Outcome) -> List<&2, U32>:
  match parts:
    case Some{T.Parts{state, body}}:
      root_limit(c, LimitWords.convert(R.limit_state(S.limits(c))), state, registry, metadata, body)
    case _: [2]

def registry_parts(~c: S.Configuration, parts: Maybe<&2, T.Parts>, metadata: Codec.Outcome) -> List<&2, U32>:
  match parts:
    case Some{T.Parts{registry, rest}}: root_parts(c, T.separate(rest), decode_registry(registry), metadata)
    case _: [2]

def parts(~c: S.Configuration, parts: Maybe<&2, T.Parts>) -> List<&2, U32>:
  match parts:
    case Some{T.Parts{metadata, rest}}:
      registry_parts(c, T.separate(rest), Codec.decode(metadata, B.Number64{4294967295, 4294967295}))
    case _: [2]

def packet(~c: S.Configuration, bytes: List<&2, U32>) -> List<&2, U32>:
  parts(c, T.separate(bytes))
