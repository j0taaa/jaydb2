# A registry history cannot manufacture admission evidence for a registration.
import Base
import ../../../contract/Interface.bend as I
import ../../../contract/PreparedRegistry.bend as G
import ../../../contract/Semantics.bend as S
import ../../../proof/PreparedRegistryHistory.bend as H

law false_registration_needs_no_certificate:
  for ~a: I.Environment
  for ~c: S.Configuration
  for entry: G.Entry
  H.HistoryAdmission(a, c, [H.Register{entry}])
def false_registration_needs_no_certificate(a, c, entry):
  Unit{}
