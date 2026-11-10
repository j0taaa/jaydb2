# Exact accepted-input soundness and complete rejection for composite keys.
# Key encoding is structural over ALL Char data; it does not validate Unicode.
# Unicode/name acceptance is an independent contract boundary, not assumed here.
import Base
import ./Key.bend as Key
import ../proof/Foundations.bend as F

def SegmentSound(+input: String,result: Key.Segment) -> Type:
  match result:
    case Key.Segment{part,tail}: {Key.part(part,tail) == input : String}
    case Key.BadSegment{}: Unit

def prepend_sound(+head: Char,+input: String,result: Key.Segment,correct: SegmentSound(input,result)) -> SegmentSound(SCon{'c',SCon{head,input}},Key.prepend(head,result)):
  match result:
    case Key.BadSegment{}: Unit{}
    case Key.Segment{+part,+tail}: Equal.cong(String,String,rest => SCon{'c',SCon{head,rest}},Key.part(part,tail),input,correct)

law accepted_segment_reconstructs_the_exact_input_prefix_and_remainder:
  for +input: String
  SegmentSound(input,Key.segment(input))
def accepted_segment_reconstructs_the_exact_input_prefix_and_remainder(input):
  match input:
    case SNil{}: Unit{}
    case SCon{'e',rest}: {==}
    case SCon{'c',SNil{}}: Unit{}
    case SCon{'c',SCon{+head,+rest}}: prepend_sound(head,rest,Key.segment(rest),accepted_segment_reconstructs_the_exact_input_prefix_and_remainder(rest))
    case SCon{Chr{U32{WCon{False{},_}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{False{},WCon{False{},_}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{False{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},_}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{False{},WCon{True{},WCon{False{},WCon{False{},WCon{True{},WCon{False{},_}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{False{},WCon{True{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{False{},WCon{True{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{False{},WCon{True{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{False{},WCon{True{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{False{},WCon{True{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{False{},WCon{True{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{False{},WCon{True{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{False{},WCon{True{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{False{},WCon{True{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{False{},WCon{True{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{False{},WCon{True{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{False{},WCon{True{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{False{},WCon{True{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{False{},WCon{True{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{False{},WCon{True{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{False{},WCon{True{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{False{},WCon{True{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{False{},WCon{True{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{False{},WCon{True{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{False{},WCon{True{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{False{},WCon{True{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{False{},WCon{True{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{False{},WCon{True{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{False{},WCon{True{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{True{},_}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{False{},WCon{True{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},_}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{False{},WCon{True{},WCon{False{},WCon{True{},_}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{False{},WCon{True{},WCon{True{},_}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},_}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{False{},_}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},WCon{True{},_}}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},_}}}}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{True{},WCon{False{},WCon{True{},_}}}}}},rest}: Unit{}
    case SCon{Chr{U32{WCon{True{},WCon{True{},WCon{True{},_}}}}},rest}: Unit{}

def Sound(+input: String,result: Maybe<&2,List<&2,String>>) -> Type:
  match result:
    case Some{parts}: {Key.encode(parts) == input : String}
    case None{}: Unit

def cons_sound(+part: String,+tail: String,+input: String,segment: {Key.part(part,tail) == input : String},result: Maybe<&2,List<&2,String>>,correct: Sound(tail,result)) -> Sound(SCon{'p',input},Key.cons(part,result)):
  match result:
    case None{}: Unit{}
    case Some{+parts}: Equal.cong(String,String,rest => SCon{'p',rest},Key.part(part,Key.encode(parts)),input,Equal.trans(String,Key.part(part,Key.encode(parts)),Key.part(part,tail),input,Equal.cong(String,String,rest => Key.part(part,rest),Key.encode(parts),tail,correct),segment))

def segment_decode_sound(+fuel: Nat,+input: String,result: Key.Segment,correct: SegmentSound(input,result),recursive: @+tail: String -> Sound(tail,Key.decode_fuel(fuel,tail))) -> Sound(SCon{'p',input},Key.decode_segment(result,tail => Key.decode_fuel(fuel,tail))):
  match result:
    case Key.BadSegment{}: Unit{}
    case Key.Segment{+part,+tail}: cons_sound(part,tail,input,correct,Key.decode_fuel(fuel,tail),recursive(tail))

law every_accepted_fuelled_key_decoder_result_reencodes_exactly:
  for +fuel: Nat
  for +input: String
  Sound(input,Key.decode_fuel(fuel,input))
def every_accepted_fuelled_key_decoder_result_reencodes_exactly(fuel,input):
  match fuel input:
    case 0n input: Unit{}
    case 1n+previous SNil{}: Unit{}
    case 1n+previous SCon{'z',SNil{}}: {==}
    case 1n+previous SCon{'z',SCon{head,rest}}: Unit{}
    case Succ{+previous} SCon{'p',+rest}: segment_decode_sound(previous,rest,Key.segment(rest),accepted_segment_reconstructs_the_exact_input_prefix_and_remainder(rest),+tail => every_accepted_fuelled_key_decoder_result_reencodes_exactly(previous,tail))
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},_}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{False{},_}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},_}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{True{},_}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{True{},_}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{False{},WCon{True{},_}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{True{},WCon{False{},WCon{False{},_}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{True{},WCon{False{},WCon{True{},WCon{False{},_}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{True{},WCon{False{},WCon{True{},WCon{True{},WCon{False{},_}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{True{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},_}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{True{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{True{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{True{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{True{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{True{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{True{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{True{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{True{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{True{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{True{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{True{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{True{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{True{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{True{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{True{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{True{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{True{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{True{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{True{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{True{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{True{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{True{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{True{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{False{},WCon{True{},_}}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{True{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{True{},WCon{False{},WCon{True{},_}}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{True{},WCon{False{},WCon{True{},WCon{True{},WCon{True{},WCon{True{},WCon{True{},_}}}}}}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{False{},WCon{True{},WCon{True{},_}}}}},rest}: Unit{}
    case 1n+previous SCon{Chr{U32{WCon{True{},_}}},rest}: Unit{}


def Meaning(+input: String,result: Maybe<&2,List<&2,String>>) -> Type:
  match result:
    case Some{parts}: {Key.encode(parts) == input : String}
    case None{}: @+parts: List<&2,String> -> {Key.encode(parts) == input : String} -> Empty

def reject_encoded_candidate(+input: String,+parts: List<&2,String>,actual: {Key.decode(input) == None{} : Maybe<&2,List<&2,String>>},candidate: {Key.encode(parts) == input : String}) -> Empty:
  F.none_negative_some(List<&2,String>,parts,Equal.trans(Maybe<&2,List<&2,String>>,None{},Key.decode(input),Some{parts},Equal.sym(Maybe<&2,List<&2,String>>,Key.decode(input),None{},actual),Equal.trans(Maybe<&2,List<&2,String>>,Key.decode(input),Key.decode(Key.encode(parts)),Some{parts},Equal.cong(String,Maybe<&2,List<&2,String>>,value => Key.decode(value),input,Key.encode(parts),Equal.sym(String,Key.encode(parts),input,candidate)),Key.decode_encode(parts))))

def complete_result(+input: String,result: Maybe<&2,List<&2,String>>,actual: {Key.decode(input) == result : Maybe<&2,List<&2,String>>},sound: Sound(input,result)) -> Meaning(input,result):
  match result:
    case Some{parts}: sound
    case None{}: +parts => exact => reject_encoded_candidate(input,parts,actual,exact)

# Input only: every Some re-encodes to exactly the complete original string;
# None rules out EVERY possible encoded list, using the existing public
# decode_encode theorem with its actual string-length fuel.
law actual_key_decode_accepts_all_and_only_exact_composite_key_encodings:
  for +input: String
  Meaning(input,Key.decode(input))
def actual_key_decode_accepts_all_and_only_exact_composite_key_encodings(input):
  complete_result(input,Key.decode(input),{==},every_accepted_fuelled_key_decoder_result_reencodes_exactly(1n+String.length(input),input))
