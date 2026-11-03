import Base
import ./Bytes.bend as B
import ./Data.bend as D

# Canonical format (decimal tags): 0 absent, 1 false, 2 true,
# 3 integer64, 4 UTF-8 text, 5 list, 6 record. Lengths and
# counts use big-endian u64. A record name uses text with tag 4.
# None means an invalid value or unrepresentable length; there is never
# truncation, length wraparound or a partial response.

def concatenate_optional(a: Maybe<&2, List<&2, U32>>, b: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match a b:
    case Some{xs} Some{ys}:
      Some{B.concatenate(xs, ys)}
    case _ _:
      None{}

def prefix_size(tag: U32, size: Maybe<&2, List<&2, U32>>, content: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match size:
    case None{}:
      None{}
    case Some{header}:
      Some{Con{tag, B.concatenate(header, content)}}

def field_variable(tag: U32, n: Nat, content: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  prefix_size(tag, B.length64(n), content)

def text_cases(valid: Bool, +bytes: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match valid:
    case False{}:
      None{}
    case True{}:
      field_variable(4, B.length(bytes), bytes)

def text(+s: String) -> Maybe<&2, List<&2, U32>>:
  text_cases(B.text_valid(s), B.utf8(s))

type Partial is Data:
  Impossible{}
  Atom{bytes: List<&2, U32>}
  ListFrame{number: Nat, bytes: List<&2, U32>}
  Record{number: Nat, bytes: List<&2, U32>}

def finalize(p: Partial) -> Maybe<&2, List<&2, U32>>:
  match p:
    case Impossible{}:
      None{}
    case Atom{bytes}:
      Some{bytes}
    case ListFrame{n, bytes}:
      field_variable(5, n, bytes)
    case Record{n, bytes}:
      field_variable(6, n, bytes)

def atom_optional(p: Maybe<&2, List<&2, U32>>) -> Partial:
  match p:
    case None{}:
      Impossible{}
    case Some{bytes}:
      Atom{bytes}

def boolean(b: Bool) -> Partial:
  match b:
    case False{}:
      Atom{[1]}
    case True{}:
      Atom{[2]}

def list_cases(h: Maybe<&2, List<&2, U32>>, t: Partial) -> Partial:
  match h t:
    case Some{head} ListFrame{n, tail}:
      ListFrame{1n+n, B.concatenate(head, tail)}
    case _ _:
      Impossible{}

def record_cases(n: Maybe<&2, List<&2, U32>>, v: Maybe<&2, List<&2, U32>>, r: Partial) -> Partial:
  match n v r:
    case Some{name} Some{value} Record{q, rest}:
      Record{1n+q, B.concatenate(name, B.concatenate(value, rest))}
    case _ _ _:
      Impossible{}

def encode_partial(v: D.Value) -> Partial:
  match v:
    case D.VAbsent{}:
      Atom{[0]}
    case D.VBool{b}:
      boolean(b)
    case D.VInt{high, low}:
      Atom{Con{3, B.be64(high, low)}}
    case D.VText{s}:
      atom_optional(text(s))
    case D.VListEmpty{}:
      ListFrame{0n, Nil{}}
    case D.VList{h, t}:
      list_cases(finalize(encode_partial(h)), encode_partial(t))
    case D.VRecordEmpty{}:
      Record{0n, Nil{}}
    case D.VRecord{n, v, r}:
      record_cases(text(n), finalize(encode_partial(v)), encode_partial(r))

def encode_cases(valid: Bool, result: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match valid:
    case False{}:
      None{}
    case True{}:
      result

def encode(+v: D.Value) -> Maybe<&2, List<&2, U32>>:
  encode_cases(D.value_valid(v), finalize(encode_partial(v)))

def representable_result(r: Maybe<&2, List<&2, U32>>) -> Bool:
  match r:
    case None{}:
      False{}
    case Some{bytes}:
      True{}

def representable(v: D.Value) -> Bool:
  representable_result(encode(v))

def Encoding(v: D.Value, bytes: List<&2, U32>) -> Type:
  {encode(v) == Some{bytes} : Maybe<&2, List<&2, U32>>}

# Decoding means finding exactly one value whose canonical
# encoding matches all bytes. This relation rejects extra bytes,
# UTF-8 variants, unordered records and duplicate names.
def Decoding(bytes: List<&2, U32>, v: D.Value) -> Type:
  Encoding(v, bytes)

def frame_content(+bytes: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  concatenate_optional(B.length64(B.length(bytes)), Some{bytes})

def frame_result(r: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match r:
    case None{}:
      None{}
    case Some{bytes}:
      frame_content(bytes)

def frame(v: D.Value) -> Maybe<&2, List<&2, U32>>:
  frame_result(encode(v))

def Message(v: D.Value, bytes: List<&2, U32>) -> Type:
  {frame(v) == Some{bytes} : Maybe<&2, List<&2, U32>>}

# The textual identity of code/proof includes every character; its
# dependency closure belongs to the core admission contract.
type Request is Data:
  Request{credential: String, code: String, arguments: D.Value, proof: String}

def request_value(r: Request) -> D.Value:
  Request{credential, code, arguments, proof} = r
  D.VRecord{"arguments", arguments,
    D.VRecord{"code", D.VText{code},
      D.VRecord{"credential", D.VText{credential},
        D.VRecord{"proof", D.VText{proof}, D.VRecordEmpty{}}}}}

def RequestEncoded(r: Request, bytes: List<&2, U32>) -> Type:
  Message(request_value(r), bytes)

type Status is Data:
  Input{}
  Authentication{}
  Certificate{}
  DataError{}
  Limit{}
  Failure{}
  Refusal{}
  Success{}

def status_text(s: Status) -> String:
  match s:
    case Input{}:
      "input"
    case Authentication{}:
      "authentication"
    case Certificate{}:
      "certificate"
    case DataError{}:
      "data"
    case Limit{}:
      "limit"
    case Failure{}:
      "failure"
    case Refusal{}:
      "refusal"
    case Success{}:
      "success"

type Response is Data:
  Response{status: Status, value: D.Value}

def response_value(r: Response) -> D.Value:
  Response{s, v} = r
  D.VRecord{"status", D.VText{status_text(s)},
    D.VRecord{"value", v, D.VRecordEmpty{}}}

def value_response_valid(s: Status, v: D.Value) -> Bool:
  match s v:
    case Success{} _:
      D.value_valid(v)
    case Refusal{} _:
      D.value_valid(v)
    case _ D.VAbsent{}:
      True{}
    case _ _:
      False{}

def response_is_valid(r: Response) -> Bool:
  Response{s, v} = r
  value_response_valid(s, v)

def ResponseEncoded(+r: Response, bytes: List<&2, U32>) -> Type:
  {response_is_valid(r) == True{} : Bool} &
  Message(response_value(r), bytes)
