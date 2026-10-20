module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ScalarQuotient.Determinant.Invariance
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ScalarQuotient.Determinant.ShortExact
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Filtration
public import ReasLib.RingTheory.Module.Support.Minimal

@[expose] public section

open scoped BigOperators

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

/-- The scalar-quotient determinant of a finite module with one-dimensional support is the
product of the determinants of its minimal-prime quotients, weighted by their localized lengths. -/
theorem scalarQuotientDeterminant_eq_prod_minimalSupport
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (a b : A) (ha : IsSMulRegular M a) (hb : IsSMulRegular M b)
    (hdim : Module.supportDim A M = 1) {t : ℕ}
    (q : Fin t → PrimeSpectrum A) (hq_injective : Function.Injective q)
    (hq_minimal : ∀ i, Minimal (· ∈ Module.support A M) (q i))
    (hq_complete : ∀ p, Minimal (· ∈ Module.support A M) p → ∃ i, q i = p) :
    scalarQuotientDeterminant M a b ha hb hdim =
      ∏ i, scalarQuotientDeterminant (A ⧸ (q i).asIdeal) a b
          (IsSMulRegular.quotient_of_minimalSupport M ha (q i) (hq_minimal i))
          (IsSMulRegular.quotient_of_minimalSupport M hb (q i) (hq_minimal i))
          (Module.supportDim_quotient_eq_one_of_minimalSupport M hdim (q i)
            (hq_minimal i)) ^
        (Module.length (Localization.AtPrime (q i).asIdeal)
          (LocalizedModule.AtPrime (q i).asIdeal M)).toNat := sorry

end CategoryTheory.TwoPeriodicEndomorphism
