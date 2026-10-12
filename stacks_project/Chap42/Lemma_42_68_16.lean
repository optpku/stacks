/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.EqualDifferential
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory HomologicalComplex

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

variable {R : Type u} [CommRing R] [IsLocalRing R]

/- Lemma 42.68.16 (1): an exact finite-length two-periodic endomorphism complex
with equal differentials has length twice the length of their common range. -/
@[stacks 02PM] #check
  (CategoryTheory.TwoPeriodicEndomorphism.length_eq_two_mul_range :
    ∀ (K : TwoPeriodicEndomorphism (ModuleCat.{v} R))
        (hM : IsFiniteLength R K.X) (hK : K.toCochainComplex.Acyclic)
        (h_eq : K.d₀ = K.d₁),
      Module.length R K.X = 2 * Module.length R (LinearMap.range K.d₀.hom))

/- Lemma 42.68.16 (2): the determinant of an exact finite-length two-periodic
endomorphism complex with equal differentials is the parity sign of their common range. -/
@[stacks 02PM] #check
  (CategoryTheory.TwoPeriodicEndomorphism.determinant_eq_neg_one_pow_range :
    ∀ (K : TwoPeriodicEndomorphism (ModuleCat.{v} R))
        (hM : IsFiniteLength R K.X) (hK : K.toCochainComplex.Acyclic)
        (h_eq : K.d₀ = K.d₁),
      determinant K hM hK =
        (-1) ^ (Module.length R (LinearMap.range K.d₀.hom)).toNat)

/- Lemma 42.68.16 (3): the determinant of an exact finite-length two-periodic
endomorphism complex with equal differentials is the parity sign of half its length. -/
@[stacks 02PM] #check
  (CategoryTheory.TwoPeriodicEndomorphism.determinant_eq_neg_one_pow_half_length :
    ∀ (K : TwoPeriodicEndomorphism (ModuleCat.{v} R))
        (hM : IsFiniteLength R K.X) (hK : K.toCochainComplex.Acyclic)
        (h_eq : K.d₀ = K.d₁),
      determinant K hM hK = (-1) ^ ((Module.length R K.X).toNat / 2))

end CategoryTheory.TwoPeriodicEndomorphism
