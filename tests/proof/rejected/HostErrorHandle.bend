import Base
import ../../../contract/HostErrors.bend as Errors
import ../../../contract/Semantics.bend as S

law false:
  {Errors.status("HANDLE") == S.Certificate{} : S.Status}
def false(): {==}
