# Equivalent input composition with checked fast natural-to-u64 conversion.
# The original input machine, decoder, authentication and error order remain
# the reference. proof/OptimizedInput proves exact equality without premises.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/Requirements.bend as R
import ./Input.bend as E
import ./Transport.bend as T
import ./FastBytes.bend as F

def parts(parts: Maybe<&2, T.Parts>, schema: D.Schema, +limits: S.Limits) -> E.PreAuthentication:
  match parts:
    case None{}:
      E.ErrorTransport{}
    case Some{T.Parts{state, body}}:
      E.read_state(F.nat64_checked(R.limit_state(limits)), schema, state, body,
        F.nat64_checked(R.limit_message(limits)))

def decode(bytes: List<&2, U32>, schema: D.Schema, limits: S.Limits) -> E.PreAuthentication:
  parts(T.separate(bytes), schema, limits)

def analyze(bytes: List<&2, U32>, schema: D.Schema, limits: S.Limits) -> E.Analysis:
  E.authenticate_pre(decode(bytes, schema, limits))
