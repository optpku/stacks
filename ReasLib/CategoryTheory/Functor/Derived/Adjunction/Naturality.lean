/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import ReasLib.CategoryTheory.Functor.Derived.Adjunction.Restriction
public import ReasLib.CategoryTheory.Functor.Derived.Naturality.Left
public import ReasLib.CategoryTheory.Functor.Derived.Naturality.Right

/-!
# Naturality of Total-Derived Adjunctions

Canonical total left and right derived transformations preserve the mate relation between
natural transformations of the original adjoint pairs.  This is independent of any particular
localization model or source of adjunctions.
-/

@[expose] public section

noncomputable section

universe uC₁ uC₂ uD₁ uD₂ vC₁ vC₂ vD₁ vD₂

namespace CategoryTheory.Adjunction.TotalDerived

variable {C₁ : Type uC₁} {C₂ : Type uC₂}
variable {D₁ : Type uD₁} {D₂ : Type uD₂}
variable [Category.{vC₁} C₁] [Category.{vC₂} C₂]
variable [Category.{vD₁} D₁] [Category.{vD₂} D₂]

variable {G₁ G₂ : C₁ ⥤ C₂} {F₁ F₂ : C₂ ⥤ C₁}
variable (adj₁ : G₁ ⊣ F₁) (adj₂ : G₂ ⊣ F₂)

variable {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂}
variable (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
variable [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]

variable [(G₁ ⋙ L₂).HasLeftDerivedFunctor W₁]
variable [(G₂ ⋙ L₂).HasLeftDerivedFunctor W₁]
variable [(F₁ ⋙ L₁).HasRightDerivedFunctor W₂]
variable [(F₂ ⋙ L₁).HasRightDerivedFunctor W₂]
variable [HasPair (G := G₁) (F := F₁) W₁ W₂ (L1 := L₁) (L2 := L₂)]
variable [HasPair (G := G₂) (F := F₂) W₁ W₂ (L1 := L₁) (L2 := L₂)]

/-- Taking canonical total derived functors preserves conjugate natural transformations between
adjoint pairs. -/
@[stacks 0BYX "mate compatibility of total-derived transformations"]
theorem conjugateEquiv_derivedNatTrans (t : G₂ ⟶ G₁) :
    conjugateEquiv
        (HasPair.derived adj₁ W₁ W₂)
        (HasPair.derived adj₂ W₁ W₂)
        (Functor.LeftDerived.mapNatTrans L₁ W₁ (Functor.whiskerRight t L₂)) =
      Functor.RightDerived.mapNatTrans L₂ W₂
        (Functor.whiskerRight (conjugateEquiv adj₁ adj₂ t) L₁) := sorry

end CategoryTheory.Adjunction.TotalDerived
