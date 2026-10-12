/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Determinant

/-!
# Two-periodic complexes with equal differentials

Length and determinant formulas for exact finite-length two-periodic endomorphism complexes whose
two differentials agree.
-/

@[expose] public section

noncomputable section

open CategoryTheory HomologicalComplex

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- An exact finite-length two-periodic endomorphism complex with equal differentials has length
twice the length of their common range. -/
theorem length_eq_two_mul_range
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R))
    (hM : IsFiniteLength R K.X) (hK : K.toCochainComplex.Acyclic)
    (h_eq : K.d₀ = K.d₁) :
    Module.length R K.X = 2 * Module.length R (LinearMap.range K.d₀.hom) := sorry

/-- The determinant of an exact finite-length two-periodic endomorphism complex with equal
differentials is the parity sign of their common range. -/
theorem determinant_eq_neg_one_pow_range
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R))
    (hM : IsFiniteLength R K.X) (hK : K.toCochainComplex.Acyclic)
    (h_eq : K.d₀ = K.d₁) :
    determinant K hM hK =
      (-1) ^ (Module.length R (LinearMap.range K.d₀.hom)).toNat := sorry

/-- The determinant of an exact finite-length two-periodic endomorphism complex with equal
differentials is the parity sign of half its length. -/
theorem determinant_eq_neg_one_pow_half_length
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R))
    (hM : IsFiniteLength R K.X) (hK : K.toCochainComplex.Acyclic)
    (h_eq : K.d₀ = K.d₁) :
    determinant K hM hK = (-1) ^ ((Module.length R K.X).toNat / 2) := sorry

end CategoryTheory.TwoPeriodicEndomorphism
