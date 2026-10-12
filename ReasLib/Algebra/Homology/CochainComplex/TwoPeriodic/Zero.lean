/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic

/-!
# Two-Periodic Endomorphism Complexes with Zero First Differential

This file defines a two-periodic endomorphism complex with first differential zero and records
the computation of its underlying object and differentials.
-/

@[expose] public section

open CategoryTheory Limits

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {X : C}

/-- The two-periodic endomorphism complex with first differential zero and second
differential `ψ`. -/
def ofZero (ψ : X ⟶ X) : TwoPeriodicEndomorphism C where
  X := X
  d₀ := 0
  d₁ := ψ
  d₀_d₁ := zero_comp
  d₁_d₀ := comp_zero

/-- The underlying object of `ofZero ψ` is the domain of `ψ`. -/
@[simp]
theorem ofZero_X (ψ : X ⟶ X) : (ofZero ψ).X = X := sorry

/-- The first differential of `ofZero ψ` is zero. -/
@[simp]
theorem ofZero_d₀ (ψ : X ⟶ X) : (ofZero ψ).d₀ = 0 := sorry

/-- The second differential of `ofZero ψ` is `ψ`. -/
@[simp]
theorem ofZero_d₁ (ψ : X ⟶ X) : (ofZero ψ).d₁ = ψ := sorry

end CategoryTheory.TwoPeriodicEndomorphism
