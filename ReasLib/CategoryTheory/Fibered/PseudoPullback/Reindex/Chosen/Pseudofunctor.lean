/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Reindex.Chosen.Construction
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Reindex.Explicit.Pseudofunctor
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory.Limits
open CategoricalPullback
open Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor
open scoped CategoricalPullback CategoryTheory.Bicategory

universe u v

namespace CategoryTheory

namespace FiberedCategoryOver.PseudoPullback.reindex.chosen

universe w vT

variable {C : Type u} [Category.{v} C]
variable {X Y S : FiberedCategoryOver.{u, v, w, vT} C}

/-- The selected-cleavage façade of the generic pointwise pullback pseudofunctor. Its values are
the categorical pullbacks of the selected fiber functors and its arrow action is selected
componentwise reindexing. -/
@[stacks 0040 "selected pointwise fiber-pullback pseudofunctor"]
noncomputable def pseudofunctor
    (F : X ⟶ S) (G : Y ⟶ S) :
    LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat :=
  BasedCategory.PseudoPullback.reindex.explicit.pseudofunctor
    (toCartesianBasedFunctor F) (toCartesianBasedFunctor G)
    X.chosenCleavage Y.chosenCleavage S.chosenCleavage

/-- The selected modeled pseudofunctor is the explicit-cleavage modeled pseudofunctor specialized
to the cleavages selected from the three fibred projections. -/
theorem pseudofunctor.eqExplicit (F : X ⟶ S) (G : Y ⟶ S) :
    pseudofunctor F G =
      BasedCategory.PseudoPullback.reindex.explicit.pseudofunctor
        (toCartesianBasedFunctor F) (toCartesianBasedFunctor G)
        X.chosenCleavage Y.chosenCleavage S.chosenCleavage := sorry

/-- The selected modeled pseudofunctor sends a base object to the categorical pullback of its
two selected fiber functors. -/
@[simp]
theorem pseudofunctor.obj
    (F : X ⟶ S) (G : Y ⟶ S) (U : C) :
    (pseudofunctor F G).obj (LocallyDiscrete.mk (op U)) =
      Cat.of ((fiberFunctor F U) ⊡ (fiberFunctor G U)) := sorry

/-- The arrow action of the selected modeled pseudofunctor is selected componentwise
reindexing. -/
@[simp]
theorem pseudofunctor.map.toFunctor
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (f : V ⟶ U) :
    ((pseudofunctor F G).map f.op.toLoc).toFunctor =
      FiberedCategoryOver.PseudoPullback.reindex.chosen.functor F G f := sorry

/-- Objectwise action of the selected modeled pseudofunctor is selected componentwise
reindexing. -/
@[simp]
theorem pseudofunctor.map.obj
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (f : V ⟶ U)
    (P : (fiberFunctor F U) ⊡ (fiberFunctor G U)) :
    ((pseudofunctor F G).map f.op.toLoc).toFunctor.obj P =
      (FiberedCategoryOver.PseudoPullback.reindex.chosen.functor F G f).obj P := sorry

/-- Morphismwise action of the selected modeled pseudofunctor is selected componentwise
reindexing. -/
@[simp]
theorem pseudofunctor.map.hom
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (f : V ⟶ U)
    {P Q : (fiberFunctor F U) ⊡ (fiberFunctor G U)} (φ : P ⟶ Q) :
    ((pseudofunctor F G).map f.op.toLoc).toFunctor.map φ =
      (FiberedCategoryOver.PseudoPullback.reindex.chosen.functor F G f).map φ := sorry

/-- The selected modeled pseudofunctor's identity constraint is the inverse of its selected
unit comparison. -/
@[simp]
theorem pseudofunctor.mapId.hom.app
    (F : X ⟶ S) (G : Y ⟶ S) (U : C)
    (P : (fiberFunctor F U) ⊡ (fiberFunctor G U)) :
    ((pseudofunctor F G).mapIdOp U).hom.toNatTrans.app P =
      (idIso F G U).inv.app P := sorry

/-- The inverse identity constraint of the selected modeled pseudofunctor is its selected unit
comparison. -/
@[simp]
theorem pseudofunctor.mapId.inv.app
    (F : X ⟶ S) (G : Y ⟶ S) (U : C)
    (P : (fiberFunctor F U) ⊡ (fiberFunctor G U)) :
    ((pseudofunctor F G).mapIdOp U).inv.toNatTrans.app P =
      (idIso F G U).hom.app P := sorry

/-- The selected modeled pseudofunctor's composition constraint is its selected direct-to-
successive reindexing comparison. -/
@[simp]
theorem pseudofunctor.mapComp.hom.app
    (F : X ⟶ S) (G : Y ⟶ S) {U V W : C}
    (f : V ⟶ U) (g : W ⟶ V)
    (P : (fiberFunctor F U) ⊡ (fiberFunctor G U)) :
    ((pseudofunctor F G).mapCompOp f g).hom.toNatTrans.app P =
      (mapCompIso F G f g).hom.app P := sorry

/-- The inverse composition constraint of the selected modeled pseudofunctor is its selected
successive-to-direct reindexing comparison. -/
@[simp]
theorem pseudofunctor.mapComp.inv.app
    (F : X ⟶ S) (G : Y ⟶ S) {U V W : C}
    (f : V ⟶ U) (g : W ⟶ V)
    (P : (fiberFunctor F U) ⊡ (fiberFunctor G U)) :
    ((pseudofunctor F G).mapCompOp f g).inv.toNatTrans.app P =
      (mapCompIso F G f g).inv.app P := sorry

/-- The selected first projections from modeled fiber pullbacks form an indexed functor to the
selected left fiber pseudofunctor. -/
@[stacks 0040 "selected first indexed projection from modeled fiber pullbacks"]
noncomputable def fst.indexedFunctor
    (F : X ⟶ S) (G : Y ⟶ S) :
    Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor (𝟭 C)
      (pseudofunctor F G) (Functor.fiberPseudofunctor X.p) :=
  BasedCategory.PseudoPullback.reindex.explicit.fst.indexedFunctor
    (toCartesianBasedFunctor F) (toCartesianBasedFunctor G)
    X.chosenCleavage Y.chosenCleavage S.chosenCleavage

/-- Components of the selected first modeled-fiber-pullback projection are ordinary first
categorical-pullback projections. -/
@[simp]
theorem fst.indexedFunctor.app
    (F : X ⟶ S) (G : Y ⟶ S) (U : C) :
    (fst.indexedFunctor F G).app U =
      π₁ (fiberFunctor F U) (fiberFunctor G U) := sorry

/-- Naturality of the selected first modeled-fiber-pullback projection is its selected first
reindexing comparison. -/
@[simp]
theorem fst.indexedFunctor.naturality
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (f : V ⟶ U) :
    (fst.indexedFunctor F G).naturality f =
      fst.iso F G f := sorry

/-- Restricted-morphism transport through the selected first modeled-fiber-pullback projection
is first projection on morphisms. -/
@[simp]
theorem fst.indexedFunctor.mapHom
    (F : X ⟶ S) (G : Y ⟶ S)
    {U₁ U₂ V : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    {P : (fiberFunctor F U₁) ⊡ (fiberFunctor G U₁)}
    {Q : (fiberFunctor F U₂) ⊡ (fiberFunctor G U₂)}
    (φ :
      (FiberedCategoryOver.PseudoPullback.reindex.chosen.functor F G f₁).obj P ⟶
        (FiberedCategoryOver.PseudoPullback.reindex.chosen.functor F G f₂).obj Q) :
    (fst.indexedFunctor F G).mapHom f₁ f₂ φ =
      φ.fst := sorry

/-- The selected second projections from modeled fiber pullbacks form an indexed functor to the
selected right fiber pseudofunctor. -/
@[stacks 0040 "selected second indexed projection from modeled fiber pullbacks"]
noncomputable def snd.indexedFunctor
    (F : X ⟶ S) (G : Y ⟶ S) :
    Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor (𝟭 C)
      (pseudofunctor F G) (Functor.fiberPseudofunctor Y.p) :=
  BasedCategory.PseudoPullback.reindex.explicit.snd.indexedFunctor
    (toCartesianBasedFunctor F) (toCartesianBasedFunctor G)
    X.chosenCleavage Y.chosenCleavage S.chosenCleavage

/-- Components of the selected second modeled-fiber-pullback projection are ordinary second
categorical-pullback projections. -/
@[simp]
theorem snd.indexedFunctor.app
    (F : X ⟶ S) (G : Y ⟶ S) (U : C) :
    (snd.indexedFunctor F G).app U =
      π₂ (fiberFunctor F U) (fiberFunctor G U) := sorry

/-- Naturality of the selected second modeled-fiber-pullback projection is its selected second
reindexing comparison. -/
@[simp]
theorem snd.indexedFunctor.naturality
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (f : V ⟶ U) :
    (snd.indexedFunctor F G).naturality f =
      snd.iso F G f := sorry

/-- Restricted-morphism transport through the selected second modeled-fiber-pullback projection
is second projection on morphisms. -/
@[simp]
theorem snd.indexedFunctor.mapHom
    (F : X ⟶ S) (G : Y ⟶ S)
    {U₁ U₂ V : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    {P : (fiberFunctor F U₁) ⊡ (fiberFunctor G U₁)}
    {Q : (fiberFunctor F U₂) ⊡ (fiberFunctor G U₂)}
    (φ :
      (FiberedCategoryOver.PseudoPullback.reindex.chosen.functor F G f₁).obj P ⟶
        (FiberedCategoryOver.PseudoPullback.reindex.chosen.functor F G f₂).obj Q) :
    (snd.indexedFunctor F G).mapHom f₁ f₂ φ =
      φ.snd := sorry

end FiberedCategoryOver.PseudoPullback.reindex.chosen

end CategoryTheory
