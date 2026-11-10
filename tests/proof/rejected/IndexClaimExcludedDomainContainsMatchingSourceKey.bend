# Deliberately false input-content claim; must reject at the proof body.
import Base
import ../../../library/Index.bend as I
import ../../../library/Key.bend as K
import ../../../library/IndexKeyViewProofs.bend as Views
import ../../../library/ValueScalarProofs.bend as Pair



law false_reject_excluded_domain_contains_matching_source_key:
  Views.Absent(K.encode(["v"]),[I.unique(["v"],"stored")])
def false_reject_excluded_domain_contains_matching_source_key(): Pair.Both{{==},Unit{}}
