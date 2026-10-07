module

import StacksCheckRecall
import ReasLib.RingTheory.Ideal.HilbertSamuel.PrimeDecomposition

open scoped BigOperators

universe u v

/- Lemma 43.15.3: the degree-`d` Hilbert--Samuel multiplicity of a finite module over a
Noetherian local ring is the if-restricted finsum over primes `p` with
`ringKrullDim (R ⧸ p.asIdeal) = d`, weighted by the length of the localized module. -/
@[stacks 0AZX] #check
  (Ideal.HilbertSamuel.multiplicityInDegree_eq_finsum :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
      {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
      (I : Ideal R) (hI : I.IsIdealOfDefinition) (d : ℕ)
      (hd : Module.supportDim R M ≤ d),
      Ideal.HilbertSamuel.multiplicityInDegree I M d =
        ∑ᶠ p : PrimeSpectrum R,
          if ringKrullDim (R ⧸ p.asIdeal) = d then
            ((Module.length (Localization.AtPrime p.asIdeal)
              (LocalizedModule.AtPrime p.asIdeal M)).toNat : ℚ) *
              Ideal.HilbertSamuel.multiplicityInDegree I (R ⧸ p.asIdeal) d
          else 0)
