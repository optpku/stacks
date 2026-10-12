/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.TrivSqZeroExt.Ideal
public import Mathlib.RingTheory.DividedPowers.DPMorphism

@[expose] public section

universe u v

namespace DividedPowers

namespace TrivSqZeroExt

variable {A : Type u} {M : Type v}
variable [CommRing A] [AddCommGroup M] [Module A M]
variable [Module Aᵐᵒᵖ M] [IsCentralScalar A M]

/-- The ideal in `TrivSqZeroExt A M` whose first coordinate lies in `I`. -/
def ideal (M : Type v) [AddCommGroup M] [Module A M]
    [Module Aᵐᵒᵖ M] [IsCentralScalar A M] (I : Ideal A) : Ideal (TrivSqZeroExt A M) :=
  I.comap (TrivSqZeroExt.fstHom A A M).toRingHom

/-- Membership in `ideal M I` is membership of the first coordinate in `I`. -/
theorem mem_ideal_iff (I : Ideal A) (a : TrivSqZeroExt A M) :
    a ∈ ideal M I ↔ a.fst ∈ I := sorry

/-- The predecessor divided power, with index zero interpreted as zero. -/
def dpowPred {I : Ideal A} (gamma : DividedPowers I) (n : ℕ) (x : A) : A :=
  if n = 0 then 0 else gamma.dpow (n - 1) x

/-- The predecessor divided power vanishes at index zero. -/
theorem dpowPred_zero {I : Ideal A} (gamma : DividedPowers I) (x : A) :
    dpowPred gamma 0 x = 0 := sorry

/-- At a successor index, the predecessor is the preceding divided power. -/
theorem dpowPred_succ {I : Ideal A} (gamma : DividedPowers I) (n : ℕ) (x : A) :
    dpowPred gamma (n + 1) x = gamma.dpow n x := sorry

/-- The explicit divided powers on the square-zero extension ideal. -/
noncomputable def dividedPowers (M : Type v) [AddCommGroup M] [Module A M]
    [Module Aᵐᵒᵖ M] [IsCentralScalar A M] {I : Ideal A} (gamma : DividedPowers I) :
    DividedPowers (ideal M I) := by
  classical
  exact {
    dpow := fun n a =>
      if h : a ∈ ideal M I then
        TrivSqZeroExt.inl (gamma.dpow n a.fst) +
          TrivSqZeroExt.inr (dpowPred gamma n a.fst • a.snd)
      else 0
    dpow_null := by sorry
    dpow_zero := by sorry
    dpow_one := by sorry
    dpow_mem := by sorry
    dpow_add := by sorry
    dpow_mul := by sorry
    mul_dpow := by sorry
    dpow_comp := by sorry
  }

/-- The coordinate formula for the explicit divided powers on `ideal I`. -/
theorem dividedPowers_apply {I : Ideal A} (gamma : DividedPowers I)
    (n : ℕ) (x : A) (hx : x ∈ I) (z : M) :
    dividedPowers M gamma n (TrivSqZeroExt.inl x + TrivSqZeroExt.inr z) =
      TrivSqZeroExt.inl (gamma.dpow n x) +
        TrivSqZeroExt.inr (dpowPred gamma n x • z) := sorry

/-- The first-coordinate inclusion is a divided-power morphism. -/
theorem inl_isDPMorphism (M : Type v) [AddCommGroup M] [Module A M]
    [Module Aᵐᵒᵖ M] [IsCentralScalar A M] {I : Ideal A} (gamma : DividedPowers I) :
    DividedPowers.IsDPMorphism gamma (dividedPowers M gamma)
      (TrivSqZeroExt.inlHom A M) := sorry

/-- The bundled divided-power morphism carried by the first-coordinate inclusion. -/
noncomputable def inlDPMorphism (M : Type v) [AddCommGroup M] [Module A M]
    [Module Aᵐᵒᵖ M] [IsCentralScalar A M] {I : Ideal A} (gamma : DividedPowers I) :
    DividedPowers.DPMorphism gamma (dividedPowers M gamma) :=
  DividedPowers.DPMorphism.mk' (inl_isDPMorphism M gamma)

/-- The underlying ring homomorphism of the bundled inclusion morphism. -/
theorem inlDPMorphism_toRingHom (M : Type v) [AddCommGroup M] [Module A M]
    [Module Aᵐᵒᵖ M] [IsCentralScalar A M] {I : Ideal A} (gamma : DividedPowers I) :
    (inlDPMorphism M gamma).toRingHom = TrivSqZeroExt.inlHom A M := sorry

end TrivSqZeroExt

end DividedPowers
