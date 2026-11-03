# Forged internal-length regression; no global E2E/Codec test.
import Base
import ../../contract/Bytes.bend as B
import ../../contract/Data.bend as D
import ../../contract/Semantics.bend as S
import ../../contract/Resources.bend as X
import ../../contract/Interface.bend as I
import ../../contract/Logic.bend as L
import ../../src/Codec.bend as C
import ../../src/Input.bend as E
import ../../proof/InputMeasure.bend as G
import ../../proof/InputRefusals.bend as R

def forged(tag: U32) -> List<&2, U32>:
  [tag, 255, 255, 255, 255, 255, 255, 255, 255]

def state() -> D.State:
  D.State{Nil{}, Nil{}}

def configuration() -> S.Configuration:
  S.Configuration{D.Schema{Nil{}}, S.NoneLaw{},
    S.Limits{9n, 9n, 9n}, "without-instantiate-environment"}

def reception() -> X.Reception:
  X.BodyReceived{0, 9, forged(4)}

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

law error_internal_admitted_has_classification_and_justification_original:
  L.E<{E.message(C.Limit{}, state()) == E.ErrorMessage{S.Input{}} : E.PreAuthentication},
    L.E<{E.read_message(Some{B.Number64{0, 9}}, forged(4), state()) == E.ErrorMessage{S.Input{}} : E.PreAuthentication},
      I.InputInvalid(I.Serve{0n, configuration(), state(), reception()})>>
def error_internal_admitted_has_classification_and_justification_original():
  R.limit_internal_admitted_and_input_justified_original(0n, configuration(), state(), reception(),
    forged(4), B.Number64{0, 9}, B.Number64{0, 9}, {==}, {==}, {==}, {==}, {==})

law error_of_body_complete_requires_channel_resume:
  L.E<I.ClosingCorrect(I.Serve{0n, configuration(), state(), reception()}, False{}),
    {X.body_invalid() == X.RefuseContinue{S.Input{}} : X.Disposition}>
def error_of_body_complete_requires_channel_resume():
  R.body_processed_preserves_closing_original(0n, configuration(), state(), reception(), forged(4), {==})
