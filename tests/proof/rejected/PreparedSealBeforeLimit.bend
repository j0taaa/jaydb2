# A real sealing failure cannot replace the earlier receipt-overflow cause.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/PreparedLaws.bend as H
import ../../../contract/PreparedRegistry.bend as G
import ../../../contract/Semantics.bend as S
import ../../../proof/PreparedControlDispatch.bend as C

law false_seal_failure_preempts_receipt_limit:
  for initial: D.State
  for entry: G.Entry
  for before: List<&2, G.Entry>
  {C.fitting_result(False{}, False{}, initial, entry, before) ==
    H.ControlResult{initial, before, H.Error{S.Failure{}}} : H.ControlResult}
def false_seal_failure_preempts_receipt_limit(initial, entry, before):
  {==}
