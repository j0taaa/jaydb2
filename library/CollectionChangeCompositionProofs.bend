# Exact two-change linkage, derived from the initial and intermediate views.
# Reused by actual create and retirement; no final invariant is assumed.
import Base
import ./MutationStateShapeProofs.bend as Shape
import ../contract/Data.bend as D
import ./CollectionFrameProofs.bend as Frame
import ./CollectionSwapProofs.bend as Swap
import ../proof/Foundations.bend as F

def intermediate_rows_are_exact(+collection: D.Collection,+initial: D.State,+old: List<&2,D.Row>,+first: List<&2,D.Row>,+observed: List<&2,D.Row>,found: {D.rows_collection(collection,initial) == Some{old} : Maybe<&2,List<&2,D.Row>>},observed_view: {D.rows_collection(collection,D.swap_collection(collection,initial,first)) == Some{observed} : Maybe<&2,List<&2,D.Row>>}) -> {observed == first : List<&2,D.Row>}:
  F.some_injective(List<&2,D.Row>,observed,first,Equal.trans(Maybe<&2,List<&2,D.Row>>,Some{observed},D.rows_collection(collection,D.swap_collection(collection,initial,first)),Some{first},Equal.sym(Maybe<&2,List<&2,D.Row>>,D.rows_collection(collection,D.swap_collection(collection,initial,first)),Some{observed},observed_view),Frame.replacing_an_existing_collection_has_the_exact_new_row_view(collection,initial,old,first,found)))

def two_changes(+collection: D.Collection,+initial: D.State,+old: List<&2,D.Row>,+first: List<&2,D.Row>,+observed: List<&2,D.Row>,+transform: Shape.Transform,+next: D.State,found: {D.rows_collection(collection,initial) == Some{old} : Maybe<&2,List<&2,D.Row>>},observed_view: {D.rows_collection(collection,D.swap_collection(collection,initial,first)) == Some{observed} : Maybe<&2,List<&2,D.Row>>},actual: {next == D.swap_collection(collection,D.swap_collection(collection,initial,first),Shape.apply(transform,observed)) : D.State}) -> {next == D.swap_collection(collection,initial,Shape.apply(transform,first)) : D.State}:
  Equal.trans(D.State,next,D.swap_collection(collection,D.swap_collection(collection,initial,first),Shape.apply(transform,observed)),D.swap_collection(collection,initial,Shape.apply(transform,first)),actual,Equal.trans(D.State,D.swap_collection(collection,D.swap_collection(collection,initial,first),Shape.apply(transform,observed)),D.swap_collection(collection,D.swap_collection(collection,initial,first),Shape.apply(transform,first)),D.swap_collection(collection,initial,Shape.apply(transform,first)),Equal.cong(List<&2,D.Row>,D.State,rows => D.swap_collection(collection,D.swap_collection(collection,initial,first),Shape.apply(transform,rows)),observed,first,intermediate_rows_are_exact(collection,initial,old,first,observed,found,observed_view)),Swap.last_collection_replacement_overrides_every_prior_replacement(collection,initial,first,Shape.apply(transform,first))))
