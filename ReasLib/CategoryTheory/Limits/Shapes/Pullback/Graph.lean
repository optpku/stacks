/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal

/-!
# Graph morphisms into pullbacks

The graph construction belongs to category theory: schemes only contribute
geometric properties of the resulting morphism.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

/-- The graph of `g : X ⟶ Y` over `S`, with codomain `X ×_S Y`. -/
@[stacks 01KS]
def pullback.graph {X Y S : C} (x : X ⟶ S) (y : Y ⟶ S) (g : X ⟶ Y)
    (hg : g ≫ y = x) [HasPullback x y] :
    X ⟶ pullback x y :=
  pullback.lift (𝟙 X) g ((Category.id_comp x).trans hg.symm)

/-- The first projection of a graph morphism is the identity. -/
@[reassoc (attr := simp)]
theorem pullback.graph_fst {X Y S : C} (x : X ⟶ S) (y : Y ⟶ S) (g : X ⟶ Y)
    (hg : g ≫ y = x) [HasPullback x y] :
    pullback.graph x y g hg ≫ pullback.fst x y = 𝟙 X := sorry

/-- The second projection of a graph morphism is the original morphism. -/
@[reassoc (attr := simp)]
theorem pullback.graph_snd {X Y S : C} (x : X ⟶ S) (y : Y ⟶ S) (g : X ⟶ Y)
    (hg : g ≫ y = x) [HasPullback x y] :
    pullback.graph x y g hg ≫ pullback.snd x y = g := sorry

/-- The map from `X ×_S Y` to `Y ×_S Y` whose pullback of the diagonal is the graph of `g`. -/
@[stacks 01KS "graph base-change map"]
def pullback.graphBaseChangeMap {X Y S : C} (x : X ⟶ S) (y : Y ⟶ S)
    (g : X ⟶ Y) (hg : g ≫ y = x) [HasPullback x y] [HasPullback y y] :
    pullback x y ⟶ pullback y y :=
  pullback.map x y y y g (𝟙 Y) (𝟙 S)
    ((Category.comp_id x).trans hg.symm)
    ((Category.comp_id y).trans (Category.id_comp y).symm)

/-- The first projection of `graphBaseChangeMap` applies `g` to the first coordinate. -/
@[reassoc (attr := simp)]
theorem pullback.graphBaseChangeMap_fst {X Y S : C} (x : X ⟶ S) (y : Y ⟶ S)
    (g : X ⟶ Y) (hg : g ≫ y = x) [HasPullback x y] [HasPullback y y] :
    pullback.graphBaseChangeMap x y g hg ≫ pullback.fst y y =
      pullback.fst x y ≫ g := sorry

/-- The second projection of `graphBaseChangeMap` retains the second coordinate. -/
@[reassoc (attr := simp)]
theorem pullback.graphBaseChangeMap_snd {X Y S : C} (x : X ⟶ S) (y : Y ⟶ S)
    (g : X ⟶ Y) (hg : g ≫ y = x) [HasPullback x y] [HasPullback y y] :
    pullback.graphBaseChangeMap x y g hg ≫ pullback.snd y y =
      pullback.snd x y := sorry

/-- The graph square is the base change of the diagonal of the target morphism. -/
@[stacks 01KS "graph as a base change of the diagonal"]
theorem pullback.graph_isPullback {X Y S : C} (x : X ⟶ S) (y : Y ⟶ S)
    (g : X ⟶ Y) (hg : g ≫ y = x) [HasPullback x y] [HasPullback y y] :
    IsPullback g (pullback.graph x y g hg) (pullback.diagonal y)
      (pullback.graphBaseChangeMap x y g hg) := sorry

end CategoryTheory.Limits

namespace CategoryTheory.Over

open Limits

variable {C : Type u} [Category.{v} C] {S : C}
variable {X Y : CategoryTheory.Over S}

/-- The graph of a morphism in a slice category, as the underlying map to the chosen pullback. -/
@[stacks 01KS "graph of a slice morphism"]
noncomputable abbrev graph (g : X ⟶ Y) [HasPullback X.hom Y.hom] :
    X.left ⟶ Limits.pullback X.hom Y.hom :=
  Limits.pullback.graph X.hom Y.hom g.left (CategoryTheory.Over.w g)

/-- The first projection of the graph of a slice morphism is the identity. -/
@[reassoc (attr := simp)]
theorem graph_fst (g : X ⟶ Y) [HasPullback X.hom Y.hom] :
    graph g ≫ Limits.pullback.fst X.hom Y.hom = 𝟙 X.left := sorry

/-- The second projection of the graph of a slice morphism is the underlying morphism. -/
@[reassoc (attr := simp)]
theorem graph_snd (g : X ⟶ Y) [HasPullback X.hom Y.hom] :
    graph g ≫ Limits.pullback.snd X.hom Y.hom = g.left := sorry

/-- The graph is the unique arrow to the pullback with the expected projections. -/
theorem graph_unique (g : X ⟶ Y) [HasPullback X.hom Y.hom]
    (i : X.left ⟶ Limits.pullback X.hom Y.hom)
    (hfst : i ≫ Limits.pullback.fst X.hom Y.hom = 𝟙 X.left)
    (hsnd : i ≫ Limits.pullback.snd X.hom Y.hom = g.left) :
    i = graph g := sorry

/-- The map between the two chosen pullbacks that exhibits a slice graph as a base change of the
target diagonal. -/
noncomputable abbrev graphBaseChangeMap (g : X ⟶ Y)
    [HasPullback X.hom Y.hom] [HasPullback Y.hom Y.hom] :
    Limits.pullback X.hom Y.hom ⟶ Limits.pullback Y.hom Y.hom :=
  Limits.pullback.graphBaseChangeMap X.hom Y.hom g.left (CategoryTheory.Over.w g)

/-- The graph of a slice morphism is the base change of the target diagonal. -/
@[stacks 01KS "slice graph as a base change of the diagonal"]
theorem graph_isPullback (g : X ⟶ Y)
    [HasPullback X.hom Y.hom] [HasPullback Y.hom Y.hom] :
    IsPullback g.left (graph g) (Limits.pullback.diagonal Y.hom)
      (graphBaseChangeMap g) := sorry

end CategoryTheory.Over
