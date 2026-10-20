/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.DescentData.Chosen
public import ReasLib.CategoryTheory.Sites.Descent.IndexedFunctor.DescentData.PullFunctor

/-!
# Change of indexing family for cartesian descent-data transport

This module compares explicit- and selected-cleavage descent-data transport with
pullback along a map of indexing families.
-/

@[expose] public section

universe t t' uC vC uS₁ vS₁ uS₂ vS₂

namespace CategoryTheory

open Functor Opposite
open scoped CategoryTheory.Bicategory

namespace CartesianBasedFunctor

variable {C : Type uC} [Category.{vC} C]
variable {S₁ : Type uS₁} {S₂ : Type uS₂}
variable [Category.{vS₁} S₁] [Category.{vS₂} S₂]
variable {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C}
variable {ι : Type t} {S : C} {X : ι → C} (a : ∀ i, X i ⟶ S)

section PullFunctor

variable {ι' : Type t'} {S' : C} {X' : ι' → C}
variable (a' : ∀ j, X' j ⟶ S')
variable {α : ι' → ι} {p : S' ⟶ S}
variable {p' : ∀ j, X' j ⟶ X (α j)}
variable (w : ∀ j, p' j ≫ a (α j) = a' j ≫ p)

/-- The explicit-cleavage descent-data functor commutes with pullback to another indexing
family. -/
noncomputable def Descent.explicit.pullFunctorIso
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage) :
    Pseudofunctor.DescentData.pullFunctor χ₁.toPseudofunctor w ⋙
        CartesianBasedFunctor.Descent.explicit.functor a' F χ₁ χ₂ ≅
      CartesianBasedFunctor.Descent.explicit.functor a F χ₁ χ₂ ⋙
        Pseudofunctor.DescentData.pullFunctor χ₂.toPseudofunctor w :=
  Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor.PullFunctor.Comparison.iso
    (Indexed.explicit.functor F χ₁ χ₂) a a' w

/-- Components of the explicit-cleavage family-pullback comparison are inverse reindexing
comparisons. -/
@[simp]
theorem Descent.explicit.pullFunctorIso.hom.component
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    (D : χ₁.toPseudofunctor.DescentData a) (j : ι') :
    ((Descent.explicit.pullFunctorIso
      (a := a) (a' := a') (w := w) F χ₁ χ₂).hom.app D).hom j =
      (Reindex.mapIso F χ₁ χ₂ (p' j) (D.obj (α j))).inv := sorry

/-- Total-category readout of a forward explicit-cleavage family-pullback comparison
component. -/
@[simp]
theorem Descent.explicit.pullFunctorIso.hom.component.val
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    (D : χ₁.toPseudofunctor.DescentData a) (j : ι') :
    (((Descent.explicit.pullFunctorIso
      (a := a) (a' := a') (w := w) F χ₁ χ₂).hom.app D).hom j).1 =
      (Reindex.mapIso F χ₁ χ₂ (p' j) (D.obj (α j))).inv.1 := sorry

/-- Inverse components of the explicit-cleavage family-pullback comparison are forward
reindexing comparisons. -/
@[simp]
theorem Descent.explicit.pullFunctorIso.inv.component
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    (D : χ₁.toPseudofunctor.DescentData a) (j : ι') :
    ((Descent.explicit.pullFunctorIso
      (a := a) (a' := a') (w := w) F χ₁ χ₂).inv.app D).hom j =
      (Reindex.mapIso F χ₁ χ₂ (p' j) (D.obj (α j))).hom := sorry

/-- Total-category readout of an inverse explicit-cleavage family-pullback comparison
component. -/
@[simp]
theorem Descent.explicit.pullFunctorIso.inv.component.val
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    (D : χ₁.toPseudofunctor.DescentData a) (j : ι') :
    (((Descent.explicit.pullFunctorIso
      (a := a) (a' := a') (w := w) F χ₁ χ₂).inv.app D).hom j).1 =
      (Reindex.mapIso F χ₁ χ₂ (p' j) (D.obj (α j))).hom.1 := sorry

/-- The selected-cleavage descent-data functor commutes with pullback to another indexing
family. -/
noncomputable def Descent.chosen.pullFunctorIso
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered] :
    Pseudofunctor.DescentData.pullFunctor
          (fiberPseudofunctor p₁) w ⋙
        CartesianBasedFunctor.Descent.chosen.functor a' F ≅
      CartesianBasedFunctor.Descent.chosen.functor a F ⋙
        Pseudofunctor.DescentData.pullFunctor
          (fiberPseudofunctor p₂) w :=
  Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor.PullFunctor.Comparison.iso
    (Indexed.chosen.functor F) a a' w

/-- Components of the selected-cleavage family-pullback comparison are inverse selected
reindexing comparisons. -/
@[simp]
theorem Descent.chosen.pullFunctorIso.hom.component
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered]
    (D : (fiberPseudofunctor p₁).DescentData a) (j : ι') :
    ((Descent.chosen.pullFunctorIso
      (a := a) (a' := a') (w := w) F).hom.app D).hom j =
      (Reindex.mapIso F
        (Cleavage.ofIsFibered p₁) (Cleavage.ofIsFibered p₂)
        (p' j) (D.obj (α j))).inv := sorry

/-- Total-category readout of a forward selected-cleavage family-pullback comparison
component. -/
@[simp]
theorem Descent.chosen.pullFunctorIso.hom.component.val
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered]
    (D : (fiberPseudofunctor p₁).DescentData a) (j : ι') :
    (((Descent.chosen.pullFunctorIso
      (a := a) (a' := a') (w := w) F).hom.app D).hom j).1 =
      (Reindex.mapIso F
        (Cleavage.ofIsFibered p₁) (Cleavage.ofIsFibered p₂)
        (p' j) (D.obj (α j))).inv.1 := sorry

/-- Inverse components of the selected-cleavage family-pullback comparison are forward
selected reindexing comparisons. -/
@[simp]
theorem Descent.chosen.pullFunctorIso.inv.component
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered]
    (D : (fiberPseudofunctor p₁).DescentData a) (j : ι') :
    ((Descent.chosen.pullFunctorIso
      (a := a) (a' := a') (w := w) F).inv.app D).hom j =
      (Reindex.mapIso F
        (Cleavage.ofIsFibered p₁) (Cleavage.ofIsFibered p₂)
        (p' j) (D.obj (α j))).hom := sorry

/-- Total-category readout of an inverse selected-cleavage family-pullback comparison
component. -/
@[simp]
theorem Descent.chosen.pullFunctorIso.inv.component.val
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered]
    (D : (fiberPseudofunctor p₁).DescentData a) (j : ι') :
    (((Descent.chosen.pullFunctorIso
      (a := a) (a' := a') (w := w) F).inv.app D).hom j).1 =
      (Reindex.mapIso F
        (Cleavage.ofIsFibered p₁) (Cleavage.ofIsFibered p₂)
        (p' j) (D.obj (α j))).hom.1 := sorry

end PullFunctor

end CartesianBasedFunctor

end CategoryTheory
