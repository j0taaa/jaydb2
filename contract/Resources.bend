# Framing, logical limits and channel continuity.
# Stages identify actual failures; they do not establish execution budgets.
import Base
import ./Semantics.bend as S
import ./Requirements.bend as R
import ./Protocol.bend as P
import ./Bytes.bend as B

type Stage is Data:
  Frame{}
  Authenticate{}
  Verify{}
  Execute{}
  Prepare{}

# Compare a declared uint64 with Nat without constructing 2^64 in Peano form.
# If Nat does not fit uint64, no uint64 declaration exceeds it.
def declared_greater_cases(+high: U32, low: U32, ceiling: Maybe<&2, B.Number64>) -> Bool:
  match ceiling:
    case None{}:
      False{}
    case Some{B.Number64{+ta, tb}}:
      U32.is_gt(high, ta) || (U32.is_eq(high, ta) && U32.is_gt(low, tb))

def declared_greater(+high: U32, low: U32, ceiling: Nat) -> Bool:
  declared_greater_cases(high, low, B.nat64(ceiling))

def declared_equal_cases(high: U32, low: U32, n: Maybe<&2, B.Number64>) -> Bool:
  match n:
    case None{}:
      False{}
    case Some{B.Number64{a, b}}:
      U32.is_eq(high, a) && U32.is_eq(low, b)

def declared_equal(high: U32, low: U32, n: Nat) -> Bool:
  declared_equal_cases(high, low, B.nat64(n))

# Reception describes bytes actually received, before value
# decoding. The environment must prove ReceptionValid for this account.
type Reception is Data:
  EOFBetweenMessages{}
  # Operator signal between calls; it cannot be forged in client bytes.
  StoppedOperator{}
  HeaderTruncated{bytes: List<&2, U32>}
  BodyTruncated{high: U32, low: U32, body: List<&2, U32>}
  BodyReceived{high: U32, low: U32, body: List<&2, U32>}

def reception_is_valid(r: Reception) -> Bool:
  match r:
    case EOFBetweenMessages{}:
      True{}
    case StoppedOperator{}:
      True{}
    case HeaderTruncated{+bs}:
      B.octets_all_valid(bs) && Nat.is_gt(B.length(bs), 0n) && Nat.is_lt(B.length(bs), 8n)
    case BodyTruncated{a, b, +bs}:
      B.octets_all_valid(bs) && declared_greater(a, b, B.length(bs))
    case BodyReceived{a, b, +bs}:
      B.octets_all_valid(bs) && declared_equal(a, b, B.length(bs))

def ReceptionValid(-r: Reception) -> Type:
  {reception_is_valid(r) == True{} : Bool}

type Disposition is Data:
  CloseWithoutResponse{}
  ProcessBody{body: List<&2, U32>}
  RefuseContinue{status: S.Status}
  RefuseClose{status: S.Status}

def truncated_cases(above: Bool) -> Disposition:
  match above:
    case True{}:
      RefuseClose{S.Limit{}}
    case False{}:
      RefuseClose{S.Input{}}

def complete_cases(above: Bool, body: List<&2, U32>) -> Disposition:
  match above:
    case True{}:
      RefuseClose{S.Limit{}}
    case False{}:
      ProcessBody{body}

def decide_reception_in(l: S.Limits, r: Reception) -> Disposition:
  match r:
    case EOFBetweenMessages{}:
      CloseWithoutResponse{}
    case StoppedOperator{}:
      CloseWithoutResponse{}
    case HeaderTruncated{bs}:
      RefuseClose{S.Input{}}
    case BodyTruncated{a, b, bs}:
      truncated_cases(declared_greater(a, b, R.limit_message(l)))
    case BodyReceived{a, b, bs}:
      complete_cases(declared_greater(a, b, R.limit_message(l)), bs)

def decide_reception(c: S.Configuration, r: Reception) -> Disposition:
  decide_reception_in(S.limits(c), r)

# A complete malformed body does not lose framing of the next
# message. This result only holds after ProcessBody.
def body_invalid() -> Disposition:
  RefuseContinue{S.Input{}}

# Delivery may fail after publication. The published state remains unchanged
# during delivery; no new rollback status is produced.
type Delivery is Data:
  Delivered{}
  DeliveryInterrupted{}

def channel_later_delivery(e: Delivery) -> Bool:
  match e:
    case Delivered{}:
      True{}
    case DeliveryInterrupted{}:
      False{}

law eof_between_messages_closes:
  for l: S.Limits
  {decide_reception_in(l, EOFBetweenMessages{}) == CloseWithoutResponse{} : Disposition}

def eof_between_messages_closes(l):
  {==}

law header_truncated_closes:
  for l: S.Limits
  for bs: List<&2, U32>
  {decide_reception_in(l, HeaderTruncated{bs}) == RefuseClose{S.Input{}} : Disposition}

def header_truncated_closes(l, bs):
  {==}

law body_malformed_complete_preserves_channel:
  {body_invalid() == RefuseContinue{S.Input{}} : Disposition}

def body_malformed_complete_preserves_channel():
  {==}
