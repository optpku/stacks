/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Reindex.Chosen.Construction.Basic
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Reindex.Explicit.Construction.Composition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition Comparison for Selected Fiber-Pullback Reindexing

This leaf owns the objectwise and natural composition comparisons for selected reindexing of
categorical pullbacks of fibers.
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

/-- The objectwise comparison from direct selected fiber-pullback reindexing along `g ≫ f` to
successive selected reindexing along `f` and `g`. -/
noncomputable def mapCompIsoApp
    (F : X ⟶ S) (G : Y ⟶ S) {U V W : C}
    (f : V ⟶ U) (g : W ⟶ V)
    (P : (fiberFunctor F U) ⊡ (fiberFunctor G U)) :
    (functor F G (g ≫ f)).obj P ≅
      (functor F G f ⋙ functor F G g).obj P :=
  BasedCategory.PseudoPullback.reindex.explicit.mapCompIsoApp
    (toCartesianBasedFunctor F) (toCartesianBasedFunctor G)
    X.chosenCleavage Y.chosenCleavage S.chosenCleavage f g P

/-- The left component of the forward selected fiber-pullback composition comparison. -/
@[simp]
theorem mapCompIsoApp.hom.fst
    (F : X ⟶ S) (G : Y ⟶ S) {U V W : C}
    (f : V ⟶ U) (g : W ⟶ V)
    (P : (fiberFunctor F U) ⊡ (fiberFunctor G U)) :
    (mapCompIsoApp F G f g P).hom.fst =
      (Functor.Chosen.Reindex.compIsoApp X.p f g P.fst).hom := by
  rfl

/-- The right component of the forward selected fiber-pullback composition comparison. -/
@[simp]
theorem mapCompIsoApp.hom.snd
    (F : X ⟶ S) (G : Y ⟶ S) {U V W : C}
    (f : V ⟶ U) (g : W ⟶ V)
    (P : (fiberFunctor F U) ⊡ (fiberFunctor G U)) :
    (mapCompIsoApp F G f g P).hom.snd =
      (Functor.Chosen.Reindex.compIsoApp Y.p f g P.snd).hom := by
  rfl

/-- The left component of the inverse selected fiber-pullback composition comparison. -/
@[simp]
theorem mapCompIsoApp.inv.fst
    (F : X ⟶ S) (G : Y ⟶ S) {U V W : C}
    (f : V ⟶ U) (g : W ⟶ V)
    (P : (fiberFunctor F U) ⊡ (fiberFunctor G U)) :
    (mapCompIsoApp F G f g P).inv.fst =
      (Functor.Chosen.Reindex.compIsoApp X.p f g P.fst).inv := by
  rfl

/-- The right component of the inverse selected fiber-pullback composition comparison. -/
@[simp]
theorem mapCompIsoApp.inv.snd
    (F : X ⟶ S) (G : Y ⟶ S) {U V W : C}
    (f : V ⟶ U) (g : W ⟶ V)
    (P : (fiberFunctor F U) ⊡ (fiberFunctor G U)) :
    (mapCompIsoApp F G f g P).inv.snd =
      (Functor.Chosen.Reindex.compIsoApp Y.p f g P.snd).inv := by
  rfl

/-- The selected objectwise fiber-pullback composition comparisons are natural. -/
theorem mapCompIsoApp.naturality.hom
    (F : X ⟶ S) (G : Y ⟶ S) {U V W : C}
    (f : V ⟶ U) (g : W ⟶ V)
    {P Q : (fiberFunctor F U) ⊡ (fiberFunctor G U)} (φ : P ⟶ Q) :
    (functor F G (g ≫ f)).map φ ≫
        (mapCompIsoApp F G f g Q).hom =
      (mapCompIsoApp F G f g P).hom ≫
        (functor F G f ⋙ functor F G g).map φ := by
  apply CategoricalPullback.hom_ext
  · exact (Functor.Chosen.Reindex.compIso X.p f g).hom.naturality φ.fst
  · exact (Functor.Chosen.Reindex.compIso Y.p f g).hom.naturality φ.snd

/-- Inverse naturality of the selected objectwise fiber-pullback composition comparison. -/
theorem mapCompIsoApp.naturality.inv
    (F : X ⟶ S) (G : Y ⟶ S) {U V W : C}
    (f : V ⟶ U) (g : W ⟶ V)
    {P Q : (fiberFunctor F U) ⊡ (fiberFunctor G U)} (φ : P ⟶ Q) :
    (functor F G f ⋙ functor F G g).map φ ≫
        (mapCompIsoApp F G f g Q).inv =
      (mapCompIsoApp F G f g P).inv ≫
        (functor F G (g ≫ f)).map φ := by
  apply CategoricalPullback.hom_ext
  · exact (Functor.Chosen.Reindex.compIso X.p f g).inv.naturality φ.fst
  · exact (Functor.Chosen.Reindex.compIso Y.p f g).inv.naturality φ.snd

/-- Direct and successive selected reindexing of categorical pullbacks of fibers are naturally
isomorphic. -/
@[stacks 0040 "selected composition comparison for fiber-pullback reindexing"]
noncomputable def mapCompIso
    (F : X ⟶ S) (G : Y ⟶ S) {U V W : C}
    (f : V ⟶ U) (g : W ⟶ V) :
    functor F G (g ≫ f) ≅
      functor F G f ⋙ functor F G g :=
  BasedCategory.PseudoPullback.reindex.explicit.mapCompIso
    (toCartesianBasedFunctor F) (toCartesianBasedFunctor G)
    X.chosenCleavage Y.chosenCleavage S.chosenCleavage f g

/-- The first component of the forward selected natural composition comparison. -/
@[simp]
theorem mapCompIso.hom.app.fst
    (F : X ⟶ S) (G : Y ⟶ S) {U V W : C}
    (f : V ⟶ U) (g : W ⟶ V)
    (P : (fiberFunctor F U) ⊡ (fiberFunctor G U)) :
    ((mapCompIso F G f g).hom.app P).fst =
      (Functor.Chosen.Reindex.compIsoApp X.p f g P.fst).hom := by
  rfl

/-- The second component of the forward selected natural composition comparison. -/
@[simp]
theorem mapCompIso.hom.app.snd
    (F : X ⟶ S) (G : Y ⟶ S) {U V W : C}
    (f : V ⟶ U) (g : W ⟶ V)
    (P : (fiberFunctor F U) ⊡ (fiberFunctor G U)) :
    ((mapCompIso F G f g).hom.app P).snd =
      (Functor.Chosen.Reindex.compIsoApp Y.p f g P.snd).hom := by
  rfl

/-- The first component of the inverse selected natural composition comparison. -/
@[simp]
theorem mapCompIso.inv.app.fst
    (F : X ⟶ S) (G : Y ⟶ S) {U V W : C}
    (f : V ⟶ U) (g : W ⟶ V)
    (P : (fiberFunctor F U) ⊡ (fiberFunctor G U)) :
    ((mapCompIso F G f g).inv.app P).fst =
      (Functor.Chosen.Reindex.compIsoApp X.p f g P.fst).inv := by
  rfl

/-- The second component of the inverse selected natural composition comparison. -/
@[simp]
theorem mapCompIso.inv.app.snd
    (F : X ⟶ S) (G : Y ⟶ S) {U V W : C}
    (f : V ⟶ U) (g : W ⟶ V)
    (P : (fiberFunctor F U) ⊡ (fiberFunctor G U)) :
    ((mapCompIso F G f g).inv.app P).snd =
      (Functor.Chosen.Reindex.compIsoApp Y.p f g P.snd).inv := by
  rfl

end FiberedCategoryOver.PseudoPullback.reindex.chosen

end CategoryTheory
