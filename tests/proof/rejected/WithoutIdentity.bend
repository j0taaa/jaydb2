import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../contract/Requirements.bend as R
import ../../../src/Core.bend as N
import ../../../proof/Safety.bend as G
import ../Certificate.bend as T

law false:
  R.SafetyTrace(N.traverse(0n, N.start(T.program(), T.context(), T.arguments(), T.initial()), S.schema(T.configuration())),
    T.configuration(), T.initial(), T.context(), T.code(), T.arguments())
def false():
  G.certificate_covers_execution_authenticated(T.configuration(), T.code(), T.program(), T.context(), T.arguments(),
    T.certificate(), T.initial(), T.initial_valid(), "invalid credential", {==}, 0n)
