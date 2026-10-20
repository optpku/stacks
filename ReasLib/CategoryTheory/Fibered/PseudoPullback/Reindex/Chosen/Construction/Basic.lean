/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.IndexedFunctor.FiberedCategoryOver.Action
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Reindex.Explicit.Construction.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Selected Reindexing of Categorical Pullbacks of Fibers

This leaf specializes pointwise categorical-pullback reindexing to the selected cleavages of
fibred categories and exposes its projection and componentwise computation API.
-/

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

/-- Reindexing of categorical pullbacks of fibers for two morphisms of fibred categories,
specialized to the selected cleavages. -/
@[stacks 0040 "selected reindexing of categorical pullbacks of fibers"]
noncomputable def functor
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (f : V ⟶ U) :
    ((fiberFunctor F U) ⊡ (fiberFunctor G U)) ⥤
      ((fiberFunctor F V) ⊡ (fiberFunctor G V)) :=
  BasedCategory.PseudoPullback.reindex.explicit.functor
    (toCartesianBasedFunctor F) (toCartesianBasedFunctor G)
    X.chosenCleavage Y.chosenCleavage S.chosenCleavage f

/-- The selected reindexing functor is the explicit-cleavage functor specialized to the
cleavages selected from the three fibred projections. -/
theorem functor.eqExplicit
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (f : V ⟶ U) :
    functor F G f =
      BasedCategory.PseudoPullback.reindex.explicit.functor
        (toCartesianBasedFunctor F) (toCartesianBasedFunctor G)
        X.chosenCleavage Y.chosenCleavage S.chosenCleavage f := sorry

/-- The first projection of selected fiber-pullback reindexing is selected reindexing in the
left fiber. -/
noncomputable def fst.iso
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (f : V ⟶ U) :
    functor F G f ⋙ π₁ (fiberFunctor F V) (fiberFunctor G V) ≅
      π₁ (fiberFunctor F U) (fiberFunctor G U) ⋙
        Functor.Chosen.reindex X.p f :=
  BasedCategory.PseudoPullback.reindex.explicit.fst.iso
    (toCartesianBasedFunctor F) (toCartesianBasedFunctor G)
    X.chosenCleavage Y.chosenCleavage S.chosenCleavage f

/-- The second projection of selected fiber-pullback reindexing is selected reindexing in the
right fiber. -/
noncomputable def snd.iso
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (f : V ⟶ U) :
    functor F G f ⋙ π₂ (fiberFunctor F V) (fiberFunctor G V) ≅
      π₂ (fiberFunctor F U) (fiberFunctor G U) ⋙
        Functor.Chosen.reindex Y.p f :=
  BasedCategory.PseudoPullback.reindex.explicit.snd.iso
    (toCartesianBasedFunctor F) (toCartesianBasedFunctor G)
    X.chosenCleavage Y.chosenCleavage S.chosenCleavage f

/-- The first object component of selected fiber-pullback reindexing. -/
@[simp]
theorem functor.obj.fst
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (f : V ⟶ U)
    (P : (fiberFunctor F U) ⊡ (fiberFunctor G U)) :
    (functor F G f |>.obj P).fst =
      (Functor.Chosen.reindex X.p f).obj P.fst := sorry

/-- The second object component of selected fiber-pullback reindexing. -/
@[simp]
theorem functor.obj.snd
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (f : V ⟶ U)
    (P : (fiberFunctor F U) ⊡ (fiberFunctor G U)) :
    (functor F G f |>.obj P).snd =
      (Functor.Chosen.reindex Y.p f).obj P.snd := sorry

/-- The structural isomorphism of selected fiber-pullback reindexing. -/
@[simp]
theorem functor.obj.iso
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (f : V ⟶ U)
    (P : (fiberFunctor F U) ⊡ (fiberFunctor G U)) :
    (functor F G f |>.obj P).iso =
      (FiberedCategoryOver.Reindex.mapIso F f P.fst).symm ≪≫
        (Functor.Chosen.reindex S.p f).mapIso P.iso ≪≫
        FiberedCategoryOver.Reindex.mapIso G f P.snd := sorry

/-- Forward-map computation for the structural isomorphism of selected fiber-pullback
reindexing. -/
@[simp]
theorem functor.obj.iso.hom
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (f : V ⟶ U)
    (P : (fiberFunctor F U) ⊡ (fiberFunctor G U)) :
    (functor F G f |>.obj P).iso.hom =
      (FiberedCategoryOver.Reindex.mapIso F f P.fst).inv ≫
        (Functor.Chosen.reindex S.p f).map P.iso.hom ≫
        (FiberedCategoryOver.Reindex.mapIso G f P.snd).hom := sorry

/-- Inverse-map computation for the structural isomorphism of selected fiber-pullback
reindexing. -/
@[simp]
theorem functor.obj.iso.inv
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (f : V ⟶ U)
    (P : (fiberFunctor F U) ⊡ (fiberFunctor G U)) :
    (functor F G f |>.obj P).iso.inv =
      (FiberedCategoryOver.Reindex.mapIso G f P.snd).inv ≫
        (Functor.Chosen.reindex S.p f).map P.iso.inv ≫
        (FiberedCategoryOver.Reindex.mapIso F f P.fst).hom := sorry

/-- The first morphism component of selected fiber-pullback reindexing. -/
@[simp]
theorem functor.map.fst
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (f : V ⟶ U)
    {P Q : (fiberFunctor F U) ⊡ (fiberFunctor G U)} (φ : P ⟶ Q) :
    (functor F G f |>.map φ).fst =
      (Functor.Chosen.reindex X.p f).map φ.fst := sorry

/-- The second morphism component of selected fiber-pullback reindexing. -/
@[simp]
theorem functor.map.snd
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (f : V ⟶ U)
    {P Q : (fiberFunctor F U) ⊡ (fiberFunctor G U)} (φ : P ⟶ Q) :
    (functor F G f |>.map φ).snd =
      (Functor.Chosen.reindex Y.p f).map φ.snd := sorry

end FiberedCategoryOver.PseudoPullback.reindex.chosen

end CategoryTheory
