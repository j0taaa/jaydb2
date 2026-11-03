# Internal packet: first block u64 length, first block and second block.
# Not a public-protocol extension; never delivered to the program.
import Base
import ../contract/Bytes.bend as B
import ./Codec.bend as C

type Parts is Data:
  Parts{first: List<&2, U32>, second: List<&2, U32>}

def invert(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      invert(t, Con{h, acc})

def divert(zero: Bool, stop: Unit -> Maybe<&2, Parts>,
  resume: Unit -> Maybe<&2, Parts>) -> Maybe<&2, Parts>:
  match zero:
    case True{}:
      stop(Unit{})
    case False{}:
      resume(Unit{})

def empty(zero: Bool, xs: List<&2, U32>) -> Maybe<&2, Parts>:
  match zero:
    case True{}:
      Some{Parts{invert(xs, Nil{}), Nil{}}}
    case False{}:
      None{}

def cut(bytes: List<&2, U32>, +count: B.Number64,
  +inverted: List<&2, U32>) -> Maybe<&2, Parts>:
  match bytes:
    case Nil{}:
      empty(C.zero64(count), inverted)
    case Con{+h, +t}:
      divert(C.zero64(count),
        unit => Some{Parts{invert(inverted, Nil{}), Con{h, t}}},
        unit => cut(t, C.decrease64(count), Con{h, inverted}))

def word(a: U32, b: U32, c: U32, d: U32) -> U32:
  (a * 16777216 + b * 65536 + c * 256 + d : U32)

def header(bytes: List<&2, U32>) -> Maybe<&2, Parts>:
  match bytes:
    case Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Con{g, Con{h, rest}}}}}}}}:
      cut(rest, B.Number64{word(a, b, c, d), word(e, f, g, h)}, Nil{})
    case _:
      None{}

def validate(ok: Bool, bytes: List<&2, U32>) -> Maybe<&2, Parts>:
  match ok:
    case False{}:
      None{}
    case True{}:
      header(bytes)

def separate(+bytes: List<&2, U32>) -> Maybe<&2, Parts>:
  validate(B.octets_all_valid(bytes), bytes)

def join_combined_header(header: Maybe<&2, List<&2, U32>>,
  first: List<&2, U32>, second: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match header:
    case None{}:
      None{}
    case Some{header}:
      Some{B.concatenate(header, B.concatenate(first, second))}

def join(+first: List<&2, U32>, second: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  join_combined_header(B.length64(B.length(first)), first, second)

law header_incomplete_negative_produces_blocks:
  {separate([0, 0, 0, 0, 0, 0, 0]) == None{} : Maybe<&2, Parts>}
def header_incomplete_negative_produces_blocks():
  {==}

law separates_without_consume_second_block:
  {separate([0, 0, 0, 0, 0, 0, 0, 2, 255, 0, 7, 8]) ==
    Some{Parts{[255, 0], [7, 8]}} : Maybe<&2, Parts>}
def separates_without_consume_second_block():
  {==}

law block_truncated_negative_becomes_block_less:
  {separate([0, 0, 0, 0, 0, 0, 0, 2, 255]) == None{} : Maybe<&2, Parts>}
def block_truncated_negative_becomes_block_less():
  {==}
