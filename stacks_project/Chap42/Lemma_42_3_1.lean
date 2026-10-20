module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Scalar.Multiplicity
import StacksCheckRecall

universe u v

/- Lemma 42.3.1: if a finite module `M` over a Noetherian local ring has support dimension
at most one, `M / xM` has support dimension at most zero, and its nonclosed support points are
the distinct primes `q i`, then the multiplicity of `(0, x)` is the sum of the orders of `x`
weighted by the lengths of the localizations of `M`. -/
@[stacks 02QF]
#check (CategoryTheory.TwoPeriodicEndomorphism.multiplicity_ofZeroScalar_eq_sum :
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (x : R) (hM : Module.supportDim R M ≤ 1)
    (hMx : Module.supportDim R (QuotSMulTop x M) ≤ 0)
    {t : ℕ} (q : Fin t → PrimeSpectrum R) (hq : Function.Injective q)
    (hq_ne_closedPoint : ∀ i, q i ≠ IsLocalRing.closedPoint R)
    (hsupport : Module.support R M =
      Set.insert (IsLocalRing.closedPoint R) (Set.range q)),
    (CategoryTheory.TwoPeriodicEndomorphism.ofZeroScalar M x).multiplicity
        (CategoryTheory.TwoPeriodicEndomorphism.ofZeroScalar_homology_isFiniteLength
          M x hM hMx 0)
        (CategoryTheory.TwoPeriodicEndomorphism.ofZeroScalar_homology_isFiniteLength
          M x hM hMx 1) =
      ∑ i, ((Ring.ord (R ⧸ (q i).asIdeal)
          (Ideal.Quotient.mk (q i).asIdeal x)).toNat : ℤ) *
        ((Module.length (Localization.AtPrime (q i).asIdeal)
          (LocalizedModule.AtPrime (q i).asIdeal M)).toNat : ℤ))
