module

public import Mathlib.Algebra.BigOperators.Finprod
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Filtration
public import ReasLib.RingTheory.Ideal.HilbertSamuel.Exact

@[expose] public section

open scoped BigOperators

universe u v

namespace Ideal.HilbertSamuel

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- The degree-`d` Hilbert--Samuel multiplicity of a finite module is the finitely supported
sum of the multiplicities of its prime quotients, weighted by the lengths of its localizations
at the primes whose quotient rings have dimension `d`. -/
theorem multiplicityInDegree_eq_finsum (I : Ideal R) (hI : I.IsIdealOfDefinition)
    (d : ℕ) (hd : Module.supportDim R M ≤ d) :
    multiplicityInDegree I M d =
      ∑ᶠ p : PrimeSpectrum R,
        if ringKrullDim (R ⧸ p.asIdeal) = d then
          ((Module.length (Localization.AtPrime p.asIdeal)
            (LocalizedModule.AtPrime p.asIdeal M)).toNat : ℚ) *
            multiplicityInDegree I (R ⧸ p.asIdeal) d
        else 0 := sorry

end Ideal.HilbertSamuel
