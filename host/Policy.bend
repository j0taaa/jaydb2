# Executed controller decisions; no OS effects or assumed validity.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Semantics.bend as S
import ../src/Codec.bend as C
import ../src/Transport.bend as T

def Bytes() -> Data:
  List<&2, U32>

type Limits is Data:
  Limits{message: B.Number64, state: B.Number64, response: B.Number64}

type Proposal is Data:
  HostRejected{}
  HostReady{response: Bytes, state: Maybe<&2, Bytes>}

type Publication is Data:
  Publication{state: Bytes, response: Bytes}

type Header is Data:
  End{}
  Terminal{status: S.Status}
  Body{size: B.Number64}

def unwrap(+bytes: Maybe<&2, Bytes>) -> Bytes:
  match bytes:
    case Some{bs}:
      bs
    case None{}:
      Nil{}
def response(+status: String, +value: D.Value) -> Bytes:
  unwrap(P.frame(D.VRecord{"status", D.VText{status}, D.VRecord{"value", value, D.VRecordEmpty{}}}))
def equal(+a: Bytes, +b: Bytes) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{h, t} Con{x, xs}:
      U32.is_eq(h, x) && equal(t, xs)
    case _ _:
      False{}
def fits_number(+n: Maybe<&2, B.Number64>, +limit: B.Number64) -> Bool:
  match n:
    case None{}:
      False{}
    case Some{n}:
      C.less_equal64(n, limit)
def fits(+bytes: Bytes, +limit: B.Number64) -> Bool:
  fits_number(B.nat64(B.length(bytes)), limit)
def word(+bytes: Bytes) -> Maybe<&2, B.Number64>:
  match bytes:
    case Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Con{g, Con{h, Nil{}}}}}}}}}:
      Some{B.Number64{T.word(a, b, c, d), T.word(e, f, g, h)}}
    case _:
      None{}
def size_bytes(+n: B.Number64) -> Bytes:
  B.Number64{a, b} = n
  B.be64(a, b)
def header_size(+fits: Bool, +n: B.Number64) -> Header:
  match fits:
    case True{}:
      Body{n}
    case False{}:
      Terminal{S.Limit{}}
def header_word(+value: Maybe<&2, B.Number64>, +limit: B.Number64) -> Header:
  match value:
    case None{}:
      Terminal{S.Input{}}
    case Some{+n}:
      header_size(C.less_equal64(n,limit),n)
def header(+bytes: Bytes, +limit: B.Number64) -> Header:
  match bytes:
    case Nil{}:
      End{}
    case Con{h,t}:
      header_word(word(Con{h,t}),limit)
def packet(+first: Bytes, +second: Bytes) -> Bytes:
  unwrap(T.join(first, second))
def error(status: S.Status) -> Bytes:
  unwrap(P.frame(S.response_value(S.response_error(status))))
def certificate_code(+code: Bytes) -> Bool:
  equal(code, B.utf8("IMPORT")) || equal(code, B.utf8("IMPORT_CYCLE")) ||
  equal(code, B.utf8("DEPENDENCY")) || equal(code, B.utf8("PARSE")) ||
  equal(code, B.utf8("META")) || equal(code, B.utf8("UNSAFE")) ||
  equal(code, B.utf8("FOREIGN")) || equal(code, B.utf8("IO")) ||
  equal(code, B.utf8("OPEN_LAW")) || equal(code, B.utf8("SHADOW")) ||
  equal(code, B.utf8("REDEFINITION")) || equal(code, B.utf8("PRIMARY_CHECK")) ||
  equal(code, B.utf8("BENDTT_CHECK")) || equal(code, B.utf8("TARGET")) ||
  equal(code, B.utf8("SOURCE_BINDING")) || equal(code, B.utf8("HOST_CAPTURE")) ||
  equal(code, B.utf8("KERNEL_CAPTURE"))
def choose(-A: Type, +value: Bool, yes: Unit -> A, no: Unit -> A) -> A:
  match value:
    case True{}:
      yes(Unit{})
    case False{}:
      no(Unit{})
def optional(-A: Data, -R: Type, +value: Maybe<&2,A>, yes: @+x: A -> R, no: Unit -> R) -> R:
  match value:
    case Some{x}:
      yes(x)
    case None{}:
      no(Unit{})
def failure(+code: Bytes) -> Bytes:
  choose(Bytes,certificate_code(code),u => error(S.Certificate{}),u => error(S.Failure{}))
# Common executed admission gate for proposed byte bounds.
def guard(ok: Bool, next: Unit -> Proposal) -> Proposal:
  match ok:
    case True{}:
      next(Unit{})
    case False{}:
      HostRejected{}

def checked_response(+parts: Maybe<&2, T.Parts>, +response: Bytes,
  +state: Maybe<&2, Bytes>, +limit: B.Number64) -> Proposal:
  match parts:
    case None{}:
      HostRejected{}
    case Some{T.Parts{body, rest}}:
      guard(equal(rest, Nil{}) && fits(body, limit),u => HostReady{response,state})
def check_state(+parts: Maybe<&2, T.Parts>, +limits: Limits) -> Proposal:
  match parts:
    case None{}:
      HostRejected{}
    case Some{T.Parts{+state, +response}}:
      Limits{m,s,r} = limits
      guard(fits(state,s),u => checked_response(T.separate(response),response,Some{state},r))
def proposal(+output: Bytes, +limits: Limits) -> Proposal:
  match output:
    case Con{0, +response}:
      Limits{m,s,r} = limits
      checked_response(T.separate(response), response, None{}, r)
    case Con{1, rest}:
      check_state(T.separate(rest), limits)
    case _:
      HostRejected{}

# Only called after the adapter has acknowledged complete worker cleanup.
def publish(+old: Bytes, +proposal: Proposal) -> Publication:
  match proposal:
    case HostRejected{}:
      Publication{old, error(S.Failure{})}
    case HostReady{response, None{}}:
      Publication{old, response}
    case HostReady{response, Some{state}}:
      Publication{state, response}
