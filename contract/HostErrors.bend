# Canonical private admission/host error codes are exact, case-sensitive text.
# Unknown (including future) codes are technical failures. No client status
# string or certificate Boolean is accepted at this boundary.
import Base
import ./Semantics.bend as S

def certificate_codes() -> List<&2, String>:
  ["IMPORT", "IMPORT_CYCLE", "DEPENDENCY", "PARSE", "META", "UNSAFE", "FOREIGN", "IO", "OPEN_LAW", "SHADOW", "REDEFINITION", "PRIMARY_CHECK", "BENDTT_CHECK", "TARGET", "SOURCE_BINDING", "HOST_CAPTURE", "KERNEL_CAPTURE"]

def contains(+code: String, codes: List<&2, String>) -> Bool:
  match codes:
    case Nil{}: False{}
    case Con{head, rest}: String.eq(code, head) || contains(code, rest)

def certificate(code: String) -> Bool:
  contains(code, certificate_codes())

def classified(certificate: Bool) -> S.Status:
  match certificate:
    case True{}: S.Certificate{}
    case False{}: S.Failure{}

def status(code: String) -> S.Status:
  classified(certificate(code))
