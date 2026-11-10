# Exact ordinary generated source environment. Client.program may legally
# capture Instance.arguments/context in concrete mode, so code text plus public
# files alone does not determine its closed denotation. No derivability or
# compiler-correctness theorem is assumed by this syntax constructor.
# As in stage.mjs, the four per-call files override available public names;
# the actual frontend's import closure still determines the loaded Book.
import Base
import ../../../../contract/Data.bend as D
import ../../../../contract/Interface.bend as I
import ../../../../contract/Protocol.bend as P
import ../../../../src/Generate.bend as Generate
import ../../../SourceService.bend as Source
import ../FrameBounds.bend as B


def generated_name(+name: String) -> Bool:
  String.eq(name, "Client.bend") || String.eq(name, "ClientProof.bend") ||
    String.eq(name, "Instance.bend") || String.eq(name, "Bindings.bend")


def remaining_file(skip: Bool, file: Source.FileSource, rest: List<&2, Source.FileSource>) -> List<&2, Source.FileSource>:
  match skip:
    case True{}: rest
    case False{}: Con{file, rest}


def public_remainder(public: List<&2, Source.FileSource>) -> List<&2, Source.FileSource>:
  match public:
    case Nil{}: Nil{}
    case Con{Source.FileSource{+name, content}, rest}:
      remaining_file(generated_name(name), Source.FileSource{name, content}, public_remainder(rest))


def exact_modules(public: List<&2, Source.FileSource>, +raw: P.Request, instance: String) -> List<&2, Source.FileSource>:
  Con{Source.FileSource{"Client.bend", I.code(raw)},
    Con{Source.FileSource{"ClientProof.bend", I.proof(raw)},
      Con{Source.FileSource{"Instance.bend", instance},
        Con{Source.FileSource{"Bindings.bend", Generate.links(I.code(raw))}, public_remainder(public)}}}}


def exact_origin(public: List<&2, Source.FileSource>, raw: P.Request, instance: String) -> Source.JudgmentSyntactic:
  Source.JudgmentSyntactic{exact_modules(public, raw, instance), "Client.bend", "Client:program"}


def ordinary_generated(public: List<&2, Source.FileSource>, raw: P.Request, instance: Maybe<&2, String>) -> Maybe<&2, Source.JudgmentSyntactic>:
  match instance:
    case None{}: None{}
    case Some{instance}: Some{exact_origin(public, raw, instance)}


def ordinary(public: List<&2, Source.FileSource>, +raw: P.Request, context: D.Context) -> Maybe<&2, Source.JudgmentSyntactic>:
  ordinary_generated(public, raw, Generate.instance(context, I.arguments(raw)))


law ordinary_closure_uses_the_actual_generated_instance_without_fallback:
  for +public: List<&2, Source.FileSource>
  for +raw: P.Request
  for +context: D.Context
  {ordinary(public, raw, context) ==
    ordinary_generated(public, raw, Generate.instance(context, I.arguments(raw))) : Maybe<&2, Source.JudgmentSyntactic>}
def ordinary_closure_uses_the_actual_generated_instance_without_fallback(public, raw, context):
  {==}


law exact_ordinary_modules_retain_the_offered_program_and_proof_and_generated_instance:
  for +public: List<&2, Source.FileSource>
  for +raw: P.Request
  for +instance: String
  {B.query(Source.FileSource, exact_modules(public, raw, instance), 2n) ==
    Some{Source.FileSource{"Instance.bend", instance}} : Maybe<&2, Source.FileSource>}
def exact_ordinary_modules_retain_the_offered_program_and_proof_and_generated_instance(public, raw, instance):
  {==}
