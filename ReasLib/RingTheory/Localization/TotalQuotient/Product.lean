module

public import ReasLib.RingTheory.Localization.TotalQuotient

/-! # The total quotient ring of a reduced ring with finitely many components -/

@[expose] public section

noncomputable section

universe u

namespace Localization

variable (R : Type u) [CommRing R] [IsReduced R]

/-- The total quotient ring decomposes as the product of the fraction fields of its
minimal-prime quotients. The inverse uses the fully proved native component decomposition. -/
def totalQuotientEquivFractionRingPi (hfinite : (minimalPrimes R).Finite) :
    totalQuotientRing R ≃+* ((q : minimalPrimes R) → FractionRing (R ⧸ q.1)) :=
  RingEquiv.ofBijective (totalQuotientToFractionRingPi R)
    (totalQuotientToFractionRingPi_bijective R hfinite)

/-- The decomposition map is the canonical coordinate localization map. -/
theorem totalQuotientEquivFractionRingPi_apply (hfinite : (minimalPrimes R).Finite)
    (z : totalQuotientRing R) :
    totalQuotientEquivFractionRingPi R hfinite z = totalQuotientToFractionRingPi R z := rfl

/-- Each coordinate of a base-ring element is its image in the corresponding fraction field. -/
theorem totalQuotientEquivFractionRingPi_algebraMap
    (hfinite : (minimalPrimes R).Finite) (r : R) (q : minimalPrimes R) :
    totalQuotientEquivFractionRingPi R hfinite
        (algebraMap R (totalQuotientRing R) r) q =
      algebraMap (R ⧸ q.1) (FractionRing (R ⧸ q.1)) (Ideal.Quotient.mk q.1 r) :=
  totalQuotientToFractionRingPi_apply R r q

end Localization
