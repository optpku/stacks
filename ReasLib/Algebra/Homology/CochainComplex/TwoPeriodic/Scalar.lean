/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Zero

/-!
# Two-Periodic Scalar Endomorphism Complexes

This file defines the two-periodic endomorphism complex whose first differential is zero and
whose second differential is scalar multiplication.
-/

@[expose] public section

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

variable {R : Type u} [CommRing R]

/-- The two-periodic endomorphism complex on `M` with first differential zero and second
differential multiplication by `x`. -/
def ofZeroScalar (M : Type v) [AddCommGroup M] [Module R M]
    (x : R) : TwoPeriodicEndomorphism (ModuleCat R) :=
  ofZero (ModuleCat.ofHom (LinearMap.lsmul R M x))

/-- The underlying module of `ofZeroScalar M x` is `M`. -/
@[simp]
theorem ofZeroScalar_X (M : Type v) [AddCommGroup M] [Module R M] (x : R) :
    (ofZeroScalar M x).X = ModuleCat.of R M := sorry

/-- The first differential of `ofZeroScalar M x` is zero. -/
@[simp]
theorem ofZeroScalar_d₀ (M : Type v) [AddCommGroup M] [Module R M] (x : R) :
    (ofZeroScalar M x).d₀ = 0 := sorry

/-- The second differential of `ofZeroScalar M x` is multiplication by `x`. -/
@[simp]
theorem ofZeroScalar_d₁ (M : Type v) [AddCommGroup M] [Module R M] (x : R) :
    (ofZeroScalar M x).d₁ = ModuleCat.ofHom (LinearMap.lsmul R M x) := sorry

end CategoryTheory.TwoPeriodicEndomorphism
