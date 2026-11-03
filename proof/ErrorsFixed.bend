# Fixed host artifacts; bytes compared with the ORIGINAL encoder.
# Asserts no status justification or chosen environment facts.
import Base
import ../contract/Semantics.bend as S
import ../contract/Protocol.bend as P

type Error is Data:
  Input{}
  Authentication{}
  Certificate{}
  DataError{}
  Limit{}
  Failure{}

def status(e: Error) -> S.Status:
  match e:
    case Input{}:
      S.Input{}
    case Authentication{}:
      S.Authentication{}
    case Certificate{}:
      S.Certificate{}
    case DataError{}:
      S.DataError{}
    case Limit{}:
      S.Limit{}
    case Failure{}:
      S.Failure{}

def bytes(e: Error) -> List<&2, U32>:
  match e:
    case Input{}:
      [0, 0, 0, 0, 0, 0, 0, 53, 6, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 6, 115, 116, 97, 116, 117, 115, 4, 0, 0, 0, 0, 0, 0, 0, 5, 105, 110, 112, 117, 116, 4, 0, 0, 0, 0, 0, 0, 0, 5, 118, 97, 108, 117, 101, 0]
    case Authentication{}:
      [0, 0, 0, 0, 0, 0, 0, 62, 6, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 6, 115, 116, 97, 116, 117, 115, 4, 0, 0, 0, 0, 0, 0, 0, 14, 97, 117, 116, 104, 101, 110, 116, 105, 99, 97, 116, 105, 111, 110, 4, 0, 0, 0, 0, 0, 0, 0, 5, 118, 97, 108, 117, 101, 0]
    case Certificate{}:
      [0, 0, 0, 0, 0, 0, 0, 59, 6, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 6, 115, 116, 97, 116, 117, 115, 4, 0, 0, 0, 0, 0, 0, 0, 11, 99, 101, 114, 116, 105, 102, 105, 99, 97, 116, 101, 4, 0, 0, 0, 0, 0, 0, 0, 5, 118, 97, 108, 117, 101, 0]
    case DataError{}:
      [0, 0, 0, 0, 0, 0, 0, 52, 6, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 6, 115, 116, 97, 116, 117, 115, 4, 0, 0, 0, 0, 0, 0, 0, 4, 100, 97, 116, 97, 4, 0, 0, 0, 0, 0, 0, 0, 5, 118, 97, 108, 117, 101, 0]
    case Limit{}:
      [0, 0, 0, 0, 0, 0, 0, 53, 6, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 6, 115, 116, 97, 116, 117, 115, 4, 0, 0, 0, 0, 0, 0, 0, 5, 108, 105, 109, 105, 116, 4, 0, 0, 0, 0, 0, 0, 0, 5, 118, 97, 108, 117, 101, 0]
    case Failure{}:
      [0, 0, 0, 0, 0, 0, 0, 55, 6, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 6, 115, 116, 97, 116, 117, 115, 4, 0, 0, 0, 0, 0, 0, 0, 7, 102, 97, 105, 108, 117, 114, 101, 4, 0, 0, 0, 0, 0, 0, 0, 5, 118, 97, 108, 117, 101, 0]

law all_os_errors_prepared_are_exactly_messages_original:
  for e: Error
  {P.frame(S.response_value(S.response_error(status(e)))) == Some{bytes(e)} : Maybe<&2, List<&2, U32>>}

def all_os_errors_prepared_are_exactly_messages_original(e):
  match e:
    case Input{}:
      {==}
    case Authentication{}:
      {==}
    case Certificate{}:
      {==}
    case DataError{}:
      {==}
    case Limit{}:
      {==}
    case Failure{}:
      {==}
