import Base
import ../../../contract/Data.bend as D
import ../../../library/Sequence.bend as Sequence
import ../../../library/SequenceGroupLookup.bend as Lookup
import ../../../library/SequenceGroupUniqueness.bend as U

law false_negative_empty_groups_satisfy_the_independent_nonempty_spec:
  U.NonemptyGroups([Sequence.Group{"a",[]}])
def false_negative_empty_groups_satisfy_the_independent_nonempty_spec():
  U.Both{{==},Unit{}}
