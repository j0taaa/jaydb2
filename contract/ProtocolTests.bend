import Base
import ./Bytes.bend as B
import ./Data.bend as D
import ./Protocol.bend as P

law utf8_multibyte:
  {B.utf8("Aç𝄞") == [65, 195, 167, 240, 157, 132, 158] : List<&2, U32>}
def utf8_multibyte():
  {==}

law utf8_maximum:
  {B.utf8_valid([244, 143, 191, 191]) == True{} : Bool}
def utf8_maximum():
  {==}

law utf8_overlong:
  {B.utf8_valid([192, 128]) == False{} : Bool}
def utf8_overlong():
  {==}

law utf8_surrogate:
  {B.utf8_valid([237, 160, 128]) == False{} : Bool}
def utf8_surrogate():
  {==}

law utf8_outside_of_domain:
  {B.utf8_valid([244, 144, 128, 128]) == False{} : Bool}
def utf8_outside_of_domain():
  {==}

law utf8_truncated:
  {B.utf8_valid([240, 159, 146]) == False{} : Bool}
def utf8_truncated():
  {==}

law utf8_negative_octet:
  {B.utf8_valid([300]) == False{} : Bool}
def utf8_negative_octet():
  {==}

law size_u64:
  {B.length64(3n) == Some{[0, 0, 0, 0, 0, 0, 0, 3]} : Maybe<&2, List<&2, U32>>}
def size_u64():
  {==}

law transport_u64:
  {B.increment64(Some{B.Number64{0, 4294967295}}) == Some{B.Number64{1, 0}} : Maybe<&2, B.Number64>}
def transport_u64():
  {==}

law overflow_u64:
  {B.increment64(Some{B.Number64{4294967295, 4294967295}}) == None{} : Maybe<&2, B.Number64>}
def overflow_u64():
  {==}

law absence_framed:
  {P.frame(D.VAbsent{}) == Some{[0, 0, 0, 0, 0, 0, 0, 1, 0]} : Maybe<&2, List<&2, U32>>}
def absence_framed():
  {==}

law list_combined_two_items:
  {P.encode(D.VList{D.VBool{False{}}, D.VList{D.VAbsent{}, D.VListEmpty{}}}) ==
   Some{[5, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0]} : Maybe<&2, List<&2, U32>>}
def list_combined_two_items():
  {==}

law rejects_tail_invalid:
  {P.encode(D.VList{D.VAbsent{}, D.VBool{False{}}}) == None{} : Maybe<&2, List<&2, U32>>}
def rejects_tail_invalid():
  {==}

law rejects_record_duplicated:
  {P.encode(D.VRecord{"a", D.VAbsent{}, D.VRecord{"a", D.VAbsent{}, D.VRecordEmpty{}}}) ==
   None{} : Maybe<&2, List<&2, U32>>}
def rejects_record_duplicated():
  {==}

law rejects_record_unordered:
  {P.encode(D.VRecord{"b", D.VAbsent{}, D.VRecord{"a", D.VAbsent{}, D.VRecordEmpty{}}}) ==
   None{} : Maybe<&2, List<&2, U32>>}
def rejects_record_unordered():
  {==}

law error_has_value_absent:
  {P.response_is_valid(P.Response{P.DataError{}, D.VText{"internal"}}) == False{} : Bool}
def error_has_value_absent():
  {==}

law success_can_have_response:
  {P.response_is_valid(P.Response{P.Success{}, D.VText{"ok"}}) == True{} : Bool}
def success_can_have_response():
  {==}
