# A registry change cannot be accepted before successful receipt preparation.
import Base
import ../../../contract/PreparedRegistry.bend as G
import ../../../proof/PreparedControlTrace.bend as T

law false_mutation_without_prepared_receipt_is_ordered:
  for before: List<&2, G.Entry>
  for after: List<&2, G.Entry>
  {T.ordered([T.RegistryChanged{before, after}], False{}) == True{} : Bool}
def false_mutation_without_prepared_receipt_is_ordered(before, after):
  {==}
