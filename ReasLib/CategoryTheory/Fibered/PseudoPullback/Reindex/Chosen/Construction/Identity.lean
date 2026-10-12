/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Reindex.Chosen.Construction.Basic
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Reindex.Explicit.Construction.Identity
import Mathlib.Tactic.CrossRefAttribute

/-!
# Identity Comparison for Selected Fiber-Pullback Reindexing

This leaf owns the objectwise and natural identity comparisons for selected reindexing of
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

/-- The objectwise unit comparison from a fiber-pullback object to its selected reindexing along
the identity base arrow. -/
noncomputable def idIsoApp
    (F : X ⟶ S) (G : Y ⟶ S) (U : C)
    (P : (fiberFunctor F U) ⊡ (fiberFunctor G U)) :
    P ≅ (functor F G (𝟙 U)).obj P :=
  BasedCategory.PseudoPullback.reindex.explicit.idIsoApp
    (toCartesianBasedFunctor F) (toCartesianBasedFunctor G)
    X.chosenCleavage Y.chosenCleavage S.chosenCleavage U P

/-- The left component of the forward selected fiber-pullback unit comparison. -/
@[simp]
theorem idIsoApp.hom.fst
    (F : X ⟶ S) (G : Y ⟶ S) (U : C)
    (P : (fiberFunctor F U) ⊡ (fiberFunctor G U)) :
    (idIsoApp F G U P).hom.fst =
      (Functor.Chosen.Reindex.idIsoApp X.p U P.fst).hom := sorry

/-- The right component of the forward selected fiber-pullback unit comparison. -/
@[simp]
theorem idIsoApp.hom.snd
    (F : X ⟶ S) (G : Y ⟶ S) (U : C)
    (P : (fiberFunctor F U) ⊡ (fiberFunctor G U)) :
    (idIsoApp F G U P).hom.snd =
      (Functor.Chosen.Reindex.idIsoApp Y.p U P.snd).hom := sorry

/-- The left component of the inverse selected fiber-pullback unit comparison. -/
@[simp]
theorem idIsoApp.inv.fst
    (F : X ⟶ S) (G : Y ⟶ S) (U : C)
    (P : (fiberFunctor F U) ⊡ (fiberFunctor G U)) :
    (idIsoApp F G U P).inv.fst =
      (Functor.Chosen.Reindex.idIsoApp X.p U P.fst).inv := sorry

/-- The right component of the inverse selected fiber-pullback unit comparison. -/
@[simp]
theorem idIsoApp.inv.snd
    (F : X ⟶ S) (G : Y ⟶ S) (U : C)
    (P : (fiberFunctor F U) ⊡ (fiberFunctor G U)) :
    (idIsoApp F G U P).inv.snd =
      (Functor.Chosen.Reindex.idIsoApp Y.p U P.snd).inv := sorry

/-- The selected objectwise fiber-pullback unit comparisons are natural. -/
theorem idIsoApp.naturality.hom
    (F : X ⟶ S) (G : Y ⟶ S) (U : C)
    {P Q : (fiberFunctor F U) ⊡ (fiberFunctor G U)} (φ : P ⟶ Q) :
    φ ≫ (idIsoApp F G U Q).hom =
      (idIsoApp F G U P).hom ≫
        (functor F G (𝟙 U)).map φ := sorry

/-- Inverse naturality of the selected objectwise fiber-pullback unit comparison. -/
theorem idIsoApp.naturality.inv
    (F : X ⟶ S) (G : Y ⟶ S) (U : C)
    {P Q : (fiberFunctor F U) ⊡ (fiberFunctor G U)} (φ : P ⟶ Q) :
    (functor F G (𝟙 U)).map φ ≫
        (idIsoApp F G U Q).inv =
      (idIsoApp F G U P).inv ≫ φ := sorry

/-- Selected reindexing of a categorical pullback of fibers along the identity is naturally
isomorphic to the identity functor. -/
@[stacks 0040 "selected identity comparison for fiber-pullback reindexing"]
noncomputable def idIso
    (F : X ⟶ S) (G : Y ⟶ S) (U : C) :
    𝟭 ((fiberFunctor F U) ⊡ (fiberFunctor G U)) ≅
      functor F G (𝟙 U) :=
  BasedCategory.PseudoPullback.reindex.explicit.idIso
    (toCartesianBasedFunctor F) (toCartesianBasedFunctor G)
    X.chosenCleavage Y.chosenCleavage S.chosenCleavage U

/-- The first component of the forward selected natural unit comparison. -/
@[simp]
theorem idIso.hom.app.fst
    (F : X ⟶ S) (G : Y ⟶ S) (U : C)
    (P : (fiberFunctor F U) ⊡ (fiberFunctor G U)) :
    ((idIso F G U).hom.app P).fst =
      (Functor.Chosen.Reindex.idIsoApp X.p U P.fst).hom := sorry

/-- The second component of the forward selected natural unit comparison. -/
@[simp]
theorem idIso.hom.app.snd
    (F : X ⟶ S) (G : Y ⟶ S) (U : C)
    (P : (fiberFunctor F U) ⊡ (fiberFunctor G U)) :
    ((idIso F G U).hom.app P).snd =
      (Functor.Chosen.Reindex.idIsoApp Y.p U P.snd).hom := sorry

/-- The first component of the inverse selected natural unit comparison. -/
@[simp]
theorem idIso.inv.app.fst
    (F : X ⟶ S) (G : Y ⟶ S) (U : C)
    (P : (fiberFunctor F U) ⊡ (fiberFunctor G U)) :
    ((idIso F G U).inv.app P).fst =
      (Functor.Chosen.Reindex.idIsoApp X.p U P.fst).inv := sorry

/-- The second component of the inverse selected natural unit comparison. -/
@[simp]
theorem idIso.inv.app.snd
    (F : X ⟶ S) (G : Y ⟶ S) (U : C)
    (P : (fiberFunctor F U) ⊡ (fiberFunctor G U)) :
    ((idIso F G U).inv.app P).snd =
      (Functor.Chosen.Reindex.idIsoApp Y.p U P.snd).inv := sorry

end FiberedCategoryOver.PseudoPullback.reindex.chosen

end CategoryTheory
