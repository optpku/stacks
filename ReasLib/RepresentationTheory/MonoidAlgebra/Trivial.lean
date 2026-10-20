/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.MonoidAlgebra.Lift

/-!
# Augmentation and trivial monoid-algebra modules
-/

@[expose] public section

open scoped MonoidAlgebra

noncomputable section

universe u w

namespace MonoidAlgebra

variable (Λ : Type u) (Γ : Type w) [Ring Λ] [Monoid Γ]

/-- The augmentation sums the coefficients of an element of the monoid algebra. -/
def augmentation : Λ[Γ] →+* Λ :=
  liftNCRingHom (RingHom.id Λ) (1 : Γ →* Λ) fun x _ ↦ Commute.one_right x

/-- The augmentation of a single monoid-algebra term is its coefficient. -/
@[simp] theorem augmentation_single (γ : Γ) (r : Λ) :
    augmentation Λ Γ (single γ r) = r := by
  simp [augmentation, liftNCRingHom_single]

/-- The coefficient module with monoid-algebra scalars restricted along the augmentation. -/
abbrev trivialModule : ModuleCat.{u} (Λ[Γ]) :=
  (ModuleCat.restrictScalars (augmentation Λ Γ)).obj (ModuleCat.of Λ Λ)

/-- Each monoid basis element with coefficient one acts trivially on the trivial module. -/
theorem trivialModule_spec (γ : Γ) (x : trivialModule Λ Γ) :
    (single γ (1 : Λ) : Λ[Γ]) • x = x := by
  change augmentation Λ Γ (single γ 1) • (show Λ from x) = x
  rw [augmentation_single, one_smul]

end MonoidAlgebra
