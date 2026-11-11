# Forged internal-length regression; no global E2E/Codec test.
import Base
import ../../contract/Bytes.bend as B
import ../../contract/Data.bend as D
import ../../contract/Semantics.bend as S
import ../../src/Codec.bend as C
import ../../src/Input.bend as E
import ../../proof/InputMeasure.bend as G

def forged(tag: U32) -> List<&2, U32>:
  [tag, 255, 255, 255, 255, 255, 255, 255, 255]

def state() -> D.State:
  D.State{Nil{}, Nil{}}

law branch_original_codec_intact_still_returns_limit:
  {C.decode(forged(4), B.Number64{0, 32768}) == C.Limit{} : C.Outcome}
def branch_original_codec_intact_still_returns_limit():
  {==}

law branch_original_nine_bytes_in_ceiling_32768_returns_input:
  {E.read_message(Some{B.Number64{0, 32768}}, forged(4), state()) == E.ErrorMessage{S.Input{}} : E.PreAuthentication}
def branch_original_nine_bytes_in_ceiling_32768_returns_input():
  G.limit_internal_in_body_admitted_and_input(forged(4), B.Number64{0, 9}, B.Number64{0, 32768},
    state(), {==}, {==}, branch_original_codec_intact_still_returns_limit())

law count_list_overflow_in_body_small_and_input:
  {E.read_message(Some{B.Number64{0, 32768}}, forged(5), state()) == E.ErrorMessage{S.Input{}} : E.PreAuthentication}
def count_list_overflow_in_body_small_and_input():
  {==}

law count_record_overflow_in_body_small_and_input:
  {E.read_message(Some{B.Number64{0, 32768}}, forged(6), state()) == E.ErrorMessage{S.Input{}} : E.PreAuthentication}
def count_record_overflow_in_body_small_and_input():
  {==}

law body_real_above_of_ceiling_preserves_limit:
  {E.read_message(Some{B.Number64{0, 1}}, [0, 0], state()) == E.ErrorMessage{S.Limit{}} : E.PreAuthentication}
def body_real_above_of_ceiling_preserves_limit():
  G.body_real_above_of_ceiling_produces_limit([0, 0], B.Number64{0, 2}, B.Number64{0, 1}, state(), {==}, {==})

law count_real_exactly_in_ceiling_negative_and_limit:
  {E.read_message(Some{B.Number64{0, 1}}, [0], state()) == E.ErrorMessage{S.Input{}} : E.PreAuthentication}
def count_real_exactly_in_ceiling_negative_and_limit():
  {==}
