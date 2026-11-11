import Base
import ../../../contract/HostErrors.bend as Errors
import ../../../contract/Semantics.bend as S

law false:
  {Errors.status("PREPARED_INTEGRITY") == S.Certificate{} : S.Status}
def false(): {==}
