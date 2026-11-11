import Base
import ../../../contract/HostErrors.bend as Errors
import ../../../contract/Semantics.bend as S

law false:
  {Errors.status("SHADOW") == S.Failure{} : S.Status}
def false(): {==}
