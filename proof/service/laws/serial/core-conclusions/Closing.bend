# Prepared conclusions need no native IO/failure premise: actual closing
# dispositions have only ordinary-mode conclusions. A queried prepared
# conclusion therefore has ClosingCorrect(False) directly from the decoder.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Interface.bend as I
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/Protocol.bend as P
import ../../../../../contract/Resources.bend as X
import ../../../../../contract/Semantics.bend as S
import ../../../../SourceService.bend as Source
import ../../../specification/ServiceLaws.bend as E
import ../../../model/EventObserver.bend as O
import ../../../model/ObservationUniqueness.bend as U
import ../../../model/FrameBounds.bend as B
import ../../../model/serial/Common.bend as C
import ../../../model/serial/Decode.bend as Decode
import ../../../model/serial/Dispatch.bend as Dispatch
import ../../../model/serial/Engine.bend as Engine
import ../../../model/serial/Chain.bend as Chain
import ../../../model/serial/GeneratedBlocks.bend as Generated
import ../observed-headers/BlockLayout.bend as Block
import ./Meaning.bend as M
import ./Algebra.bend as A
import ./Views.bend as V
import ./RuntimeBase.bend as R

def events(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +before: E.Snapshot, +disposition: X.Disposition, primitives: Dispatch.Primitives) -> List<&2, O.AuditEvent>:
  Engine.selected_events(Engine.selection(disposition), before,
    C.events(Dispatch.decoded(c, binding, public, before, Decode.disposed(c, E.database(before), disposition), primitives)))

def quiet_empty_prefix(+run: C.CallRun, none: {M.quiet(C.events(run)) == True{} : Bool}) -> {M.quiet(C.events(C.prefix([], run))) == True{} : Bool}:
  %Equal.sym(List<&2, O.AuditEvent>, C.events(C.prefix([], run)), C.events(run), A.prefix_events([], run)) : {M.quiet(_) == True{} : Bool}
  none

def impossible(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +world: Nat, +input: X.Reception, +selected: D.State, +events: List<&2, O.AuditEvent>, +index: Nat,
  +response: S.Response, +state: D.State, +closes: Bool,
  none: {M.quiet(events) == True{} : Bool},
  query: {B.query(U.View, U.values(c, binding, public, Engine.stamp(world, input, selected, events)), index) == Some{U.ConclusionView{E.Transaction{response}, state, closes}} : Maybe<&2, U.View>}) -> Empty:
  U.an_excluded_source_tag_cannot_be_queried(3n, U.values(c, binding, public, Engine.stamp(world, input, selected, events)), index, U.ConclusionView{E.Transaction{response}, state, closes},
    V.quiet(c, binding, public, world, input, selected, events, none), query, {==})

def disposed(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +world: Nat, +input: X.Reception, +before: E.Snapshot, disposition: X.Disposition, +primitives: Dispatch.Primitives,
  +index: Nat, +response: S.Response, +state: D.State, +closes: Bool,
  query: {B.query(U.View, U.values(c, binding, public, Engine.stamp(world, input, E.database(before), events(c, binding, public, before, disposition, primitives))), index) == Some{U.ConclusionView{E.Transaction{response}, state, closes}} : Maybe<&2, U.View>}) ->
  I.ClosingDisposition(disposition, False{}):
  match disposition:
    case X.CloseWithoutResponse{}:
      L.ex_false(I.ClosingDisposition(X.CloseWithoutResponse{}, False{}), impossible(c, binding, public, world, input, E.database(before), events(c, binding, public, before, X.CloseWithoutResponse{}, primitives), index, response, state, closes, {==}, query))
    case X.RefuseClose{+status}:
      L.ex_false(I.ClosingDisposition(X.RefuseClose{status}, False{}), impossible(c, binding, public, world, input, E.database(before), events(c, binding, public, before, X.RefuseClose{status}, primitives), index, response, state, closes,
        quiet_empty_prefix(C.error(False{}, "", before, status, True{}, Dispatch.send(primitives)), R.ordinary_error_framed("", before, status, True{}, Dispatch.send(primitives), P.frame(S.response_value(S.response_error(status))))), query))
    case X.RefuseContinue{status}: {==}
    case X.ProcessBody{bytes}: {==}

def computed_events(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +ordinal: Nat, +before: E.Snapshot, +input: X.Reception, +primitives: Dispatch.Primitives) ->
  {Block.events(Engine.block(c, binding, public, ordinal, before, Engine.Job{input, primitives})) == events(c, binding, public, before, X.decide_reception(c, input), primitives) : List<&2, O.AuditEvent>}:
  {==}

def for_computed(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +ordinal: Nat, +before: E.Snapshot, +input: X.Reception, +primitives: Dispatch.Primitives,
  +index: Nat, +response: S.Response, +state: D.State, +closes: Bool,
  query: {B.query(U.View, U.values(c, binding, public, Engine.block_items(Engine.block(c, binding, public, ordinal, before, Engine.Job{input, primitives}))), index) == Some{U.ConclusionView{E.Transaction{response}, state, closes}} : Maybe<&2, U.View>}) ->
  I.ClosingCorrect(I.Serve{Succ{ordinal}, c, E.database(before), input}, False{}):
  disposed(c, binding, public, Succ{ordinal}, input, before, X.decide_reception(c, input), primitives, index, response, state, closes,
    (%computed_events(c, binding, public, ordinal, before, input, primitives) :
      {B.query(U.View, U.values(c, binding, public, Engine.stamp(Succ{ordinal}, input, E.database(before), _)), index) == Some{U.ConclusionView{E.Transaction{response}, state, closes}} : Maybe<&2, U.View>}
      query))

def from_head(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +block: Engine.Block, +index: Nat, +response: S.Response, +state: D.State, +closes: Bool,
  +query: {B.query(U.View, U.values(c, binding, public, Engine.block_items(block)), index) == Some{U.ConclusionView{E.Transaction{response}, state, closes}} : Maybe<&2, U.View>},
  job: Engine.Job,
  +exact: {block == Engine.block(c, binding, public, Chain.block_ordinal(block), Chain.block_before(block), job) : Engine.Block}) ->
  I.ClosingCorrect(I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), Block.input(block)}, False{}):
  match job:
    case Engine.Job{+input, +primitives}:
      %Equal.sym(Engine.Block, block, Engine.block(c, binding, public, Chain.block_ordinal(block), Chain.block_before(block), Engine.Job{input, primitives}), exact) :
        I.ClosingCorrect(I.Serve{Engine.world(_), c, E.database(Chain.block_before(_)), Block.input(_)}, False{})
      for_computed(c, binding, public, Chain.block_ordinal(block), Chain.block_before(block), input, primitives, index, response, state, closes,
        (%exact : {B.query(U.View, U.values(c, binding, public, Engine.block_items(_)), index) == Some{U.ConclusionView{E.Transaction{response}, state, closes}} : Maybe<&2, U.View>} query))

def from_generated(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  -script: List<&2, Engine.Job>, -owner: Nat, +block: Engine.Block, +index: Nat, +response: S.Response, +state: D.State, +closes: Bool,
  +query: {B.query(U.View, U.values(c, binding, public, Engine.block_items(block)), index) == Some{U.ConclusionView{E.Transaction{response}, state, closes}} : Maybe<&2, U.View>},
  generated: Generated.GeneratedAt(c, binding, public, script, owner, block)) ->
  I.ClosingCorrect(I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), Block.input(block)}, False{}):
  match generated:
    case (+job, L.Both{job_query, exact}):
      from_head(c, binding, public, block, index, response, state, closes, query, job, exact)
