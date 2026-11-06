# Reversible composite keys. Every character is tagged, including delimiters.
# Ordinary row keys, not names; no hashing, truncation or Nat conversion.
import Base

type Segment is Data:
  Segment{part: String, rest: String}
  BadSegment{}

def part(s: String, tail: String) -> String:
  match s:
    case SNil{}: SCon{'e', tail}
    case SCon{h, rest}: SCon{'c', SCon{h, part(rest, tail)}}

def encode(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}: "z"
    case Con{s, rest}: SCon{'p', part(s, encode(rest))}

def prepend(h: Char, result: Segment) -> Segment:
  match result:
    case Segment{s, rest}: Segment{SCon{h, s}, rest}
    case BadSegment{}: BadSegment{}

def segment(s: String) -> Segment:
  match s:
    case SCon{'e', rest}: Segment{"", rest}
    case SCon{'c', SCon{h, rest}}: prepend(h, segment(rest))
    case _: BadSegment{}

def cons(s: String, result: Maybe<&2, List<&2, String>>) -> Maybe<&2, List<&2, String>>:
  match result:
    case Some{xs}: Some{Con{s, xs}}
    case None{}: None{}

def decode_segment(result: Segment, next: String -> Maybe<&2, List<&2, String>>) -> Maybe<&2, List<&2, String>>:
  match result:
    case Segment{part, tail}: cons(part, next(tail))
    case BadSegment{}: None{}

# Fuel is input character length, so malformed input always terminates too.
def decode_fuel(n: Nat, s: String) -> Maybe<&2, List<&2, String>>:
  match n s:
    case Succ{m} SCon{'z', SNil{}}: Some{Nil{}}
    case Succ{m} SCon{'p', rest}:
      decode_segment(segment(rest), tail => decode_fuel(m, tail))
    case _ _: None{}

def decode(+s: String) -> Maybe<&2, List<&2, String>>:
  decode_fuel(Succ{String.length(s)}, s)

law segment_roundtrip:
  for s: String
  for +tail: String
  {segment(part(s, tail)) == Segment{s, tail} : Segment}
def segment_roundtrip(s, tail):
  match s:
    case SNil{}: {==}
    case SCon{+h, rest}:
      %Equal.sym(Segment, segment(part(rest, tail)), Segment{rest, tail}, segment_roundtrip(rest, tail)) : {prepend(h, _) == Segment{SCon{h, rest}, tail} : Segment}
      {==}

# List-sized fuel is sufficient for an encoded key. No string length lemma
# is needed by callers who keep the list arity alongside the encoded key.
def arity(xs: List<&2, String>) -> Nat:
  match xs:
    case Nil{}: 1n
    case Con{s, rest}: Succ{arity(rest)}

law roundtrip:
  for +xs: List<&2, String>
  {decode_fuel(arity(xs), encode(xs)) == Some{xs} : Maybe<&2, List<&2, String>>}
def roundtrip(xs):
  match xs:
    case Nil{}: {==}
    case Con{+s, +rest}:
      %Equal.sym(Segment, segment(part(s, encode(rest))), Segment{s, encode(rest)}, segment_roundtrip(s, encode(rest))) : {decode_segment(_, tail => decode_fuel(arity(rest), tail)) == Some{Con{s, rest}} : Maybe<&2, List<&2, String>>}
      %Equal.sym(Maybe<&2, List<&2, String>>, decode_fuel(arity(rest), encode(rest)), Some{rest}, roundtrip(rest)) : {cons(s, _) == Some{Con{s, rest}} : Maybe<&2, List<&2, String>>}
      {==}

def nonempty(s: String) -> Bool:
  match s:
    case SCon{'p', rest}: True{}
    case _: False{}

def split(s: String) -> Segment:
  match s:
    case SCon{'p', rest}: segment(rest)
    case _: BadSegment{}

def segment_part(s: Segment) -> String:
  match s:
    case Segment{part, rest}: part
    case BadSegment{}: ""

def segment_rest(s: Segment) -> String:
  match s:
    case Segment{part, rest}: rest
    case BadSegment{}: ""

def IsTrue(b: Bool) -> Type:
  match b:
    case True{}: Unit
    case False{}: Empty

def impossible(-A: Type, e: Empty) -> A:
  match e:

def false_true(-A: Type, h: {False{} == True{} : Bool}) -> A:
  impossible(A, (%h : Bool.pick(Type, _, Empty, Unit) Unit{}))

law injective:
  for +xs: List<&2, String>
  for +ys: List<&2, String>
  for h: {encode(xs) == encode(ys) : String}
  {xs == ys : List<&2, String>}
def injective(xs, ys, h):
  match xs ys:
    case Nil{} Nil{}: {==}
    case Nil{} Con{s, rest}:
      false_true({Nil{} == Con{s, rest} : List<&2, String>}, Equal.cong(String, Bool, nonempty, "z", encode(Con{s, rest}), h))
    case Con{s, rest} Nil{}:
      false_true({Con{s, rest} == Nil{} : List<&2, String>}, Equal.sym(Bool, True{}, False{}, Equal.cong(String, Bool, nonempty, encode(Con{s, rest}), "z", h)))
    case Con{+s, +rest} Con{+t, +tail}:
      +pair = Equal.trans(Segment, Segment{s, encode(rest)}, split(encode(Con{s, rest})), Segment{t, encode(tail)},
        Equal.sym(Segment, split(encode(Con{s, rest})), Segment{s, encode(rest)}, segment_roundtrip(s, encode(rest))),
        Equal.trans(Segment, split(encode(Con{s, rest})), split(encode(Con{t, tail})), Segment{t, encode(tail)},
          Equal.cong(String, Segment, split, encode(Con{s, rest}), encode(Con{t, tail}), h), segment_roundtrip(t, encode(tail))))
      head = Equal.cong(Segment, String, segment_part, Segment{s, encode(rest)}, Segment{t, encode(tail)}, pair)
      ends = Equal.cong(Segment, String, segment_rest, Segment{s, encode(rest)}, Segment{t, encode(tail)}, pair)
      Equal.trans(List<&2, String>, Con{s, rest}, Con{t, rest}, Con{t, tail},
        Equal.cong(String, List<&2, String>, x => Con{x, rest}, s, t, head),
        Equal.cong(List<&2, String>, List<&2, String>, r => Con{t, r}, rest, tail, injective(rest, tail, ends)))

# Structural fuel evidence: enough steps remain to inspect every encoded part.
def Enough(n: Nat, xs: List<&2, String>) -> Type:
  match n xs:
    case Succ{m} Nil{}: Unit
    case Succ{m} Con{s, rest}: Enough(m, rest)
    case Zero{} _: Empty

def enough_more(n: Nat, xs: List<&2, String>, h: Enough(n, xs)) -> Enough(Succ{n}, xs):
  match n xs:
    case Zero{} xs: impossible(Enough(1n, xs), h)
    case Succ{m} Nil{}: Unit{}
    case Succ{m} Con{s, rest}: enough_more(m, rest, h)

# Segment encoding only adds characters; it cannot consume the tail's fuel.
def part_enough(s: String, +tail: String, +xs: List<&2, String>,
  h: Enough(Succ{String.length(tail)}, xs)) -> Enough(Succ{String.length(part(s, tail))}, xs):
  match s:
    case SNil{}: enough_more(Succ{String.length(tail)}, xs, h)
    case SCon{c, +rest}:
      enough_more(Succ{Succ{String.length(part(rest, tail))}}, xs,
        enough_more(Succ{String.length(part(rest, tail))}, xs, part_enough(rest, tail, xs, h)))

def encoded_enough(+xs: List<&2, String>) -> Enough(Succ{String.length(encode(xs))}, xs):
  match xs:
    case Nil{}: Unit{}
    case Con{+s, +rest}: part_enough(s, encode(rest), rest, encoded_enough(rest))

law roundtrip_enough:
  for +n: Nat
  for +xs: List<&2, String>
  for h: Enough(n, xs)
  {decode_fuel(n, encode(xs)) == Some{xs} : Maybe<&2, List<&2, String>>}
def roundtrip_enough(n, xs, h):
  match n xs:
    case Zero{} xs: impossible({decode_fuel(0n, encode(xs)) == Some{xs} : Maybe<&2, List<&2, String>>}, h)
    case Succ{m} Nil{}: {==}
    case Succ{+m} Con{+s, +rest}:
      %Equal.sym(Segment, segment(part(s, encode(rest))), Segment{s, encode(rest)}, segment_roundtrip(s, encode(rest))) : {decode_segment(_, tail => decode_fuel(m, tail)) == Some{Con{s, rest}} : Maybe<&2, List<&2, String>>}
      %Equal.sym(Maybe<&2, List<&2, String>>, decode_fuel(m, encode(rest)), Some{rest}, roundtrip_enough(m, rest, h)) : {cons(s, _) == Some{Con{s, rest}} : Maybe<&2, List<&2, String>>}
      {==}

# The public decoder's actual string-length fuel suffices for every key.
law decode_encode:
  for +xs: List<&2, String>
  {decode(encode(xs)) == Some{xs} : Maybe<&2, List<&2, String>>}
def decode_encode(xs):
  roundtrip_enough(Succ{String.length(encode(xs))}, xs, encoded_enough(xs))
