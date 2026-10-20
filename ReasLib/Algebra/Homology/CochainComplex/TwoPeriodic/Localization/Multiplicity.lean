/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Localization.Determinant
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Multiplicity

/-!
# Multiplicity from localized determinants

This file relates the multiplicity of a finite two-periodic endomorphism complex to the orders
of its determinants at the minimal points of its support.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

/-- For a finite two-periodic complex with finite-length cohomology and one-dimensional support,
the negative multiplicity is the sum of the orders of its determinants at the distinct minimal
support primes. -/
theorem neg_multiplicity_eq_sum_determinantOrderAt
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) [Module.Finite R K.X]
    (h₀ : IsFiniteLength R (K.toCochainComplex.homology 0))
    (h₁ : IsFiniteLength R (K.toCochainComplex.homology 1))
    (hdim : Module.supportDim R K.X = 1) {t : ℕ}
    (q : Fin t → PrimeSpectrum R) (hq_injective : Function.Injective q)
    (hq_minimal : ∀ i, Minimal (· ∈ Module.support R K.X) (q i))
    (hq_complete : ∀ p, Minimal (· ∈ Module.support R K.X) p → ∃ i, q i = p) :
    -K.multiplicity h₀ h₁ =
      ∑ i, K.determinantOrderAt h₀ h₁ hdim (q i) (hq_minimal i) := sorry

end CategoryTheory.TwoPeriodicEndomorphism
