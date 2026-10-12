/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Localization.Multiplicity
import StacksCheckRecall

universe u v

/- Proposition 42.68.43: for a finite two-periodic complex over a Noetherian local ring whose
cohomology has finite length and whose support has dimension one, the negative multiplicity is
the sum of the orders of the determinants localized at the distinct minimal support primes. -/
@[stacks 02QD] #check
  (CategoryTheory.TwoPeriodicEndomorphism.neg_multiplicity_eq_sum_determinantOrderAt :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (K : CategoryTheory.TwoPeriodicEndomorphism (ModuleCat.{v} R)) [Module.Finite R K.X]
    (h₀ : IsFiniteLength R (K.toCochainComplex.homology 0))
    (h₁ : IsFiniteLength R (K.toCochainComplex.homology 1))
    (hdim : Module.supportDim R K.X = 1) {t : ℕ}
    (q : Fin t → PrimeSpectrum R) (hq_injective : Function.Injective q)
    (hq_minimal : ∀ i, Minimal (· ∈ Module.support R K.X) (q i))
    (hq_complete : ∀ p, Minimal (· ∈ Module.support R K.X) p → ∃ i, q i = p),
    -K.multiplicity h₀ h₁ =
      ∑ i, K.determinantOrderAt h₀ h₁ hdim (q i) (hq_minimal i))
