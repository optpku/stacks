module

public import ReasLib.RingTheory.Flat.AssociatedPrime
import StacksCheckRecall

open scoped TensorProduct

universe u v

namespace RingHom.Flat

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  [IsNoetherianRing A] [IsNoetherianRing B]

/- Clause (1): condition (2) implies condition (1). -/
#check (And.left :
  (nonZeroDivisors A ≤ Submonoid.comap (algebraMap A B) (nonZeroDivisors B) ∧
    (Algebra.TensorProduct.includeLeft :
      FractionRing A →ₐ[A] FractionRing A ⊗[A] B).toRingHom.Flat) →
  nonZeroDivisors A ≤ Submonoid.comap (algebraMap A B) (nonZeroDivisors B))

/- Clause (2): condition (2) implies condition (4). -/
#check (RingHom.Flat.overAssociatedPrimes_of_totalQuotientBaseChange :
  (nonZeroDivisors A ≤ Submonoid.comap (algebraMap A B) (nonZeroDivisors B) ∧
    (Algebra.TensorProduct.includeLeft :
      FractionRing A →ₐ[A] FractionRing A ⊗[A] B).toRingHom.Flat) →
  (∀ q : PrimeSpectrum B, q.asIdeal ∈ associatedPrimes B B →
    (algebraMap A (Localization.AtPrime q.asIdeal)).Flat) ∧
  (∀ q : PrimeSpectrum B, q.asIdeal.under A ∈ associatedPrimes A A →
    (algebraMap A (Localization.AtPrime q.asIdeal)).Flat))

/- Clause (3): condition (3) implies condition (1). -/
#check (RingHom.Flat.preservesNonZeroDivisors_of_atAssociatedPrimes :
  (∀ q : PrimeSpectrum B, q.asIdeal ∈ associatedPrimes B B →
    (algebraMap A (Localization.AtPrime q.asIdeal)).Flat) →
  nonZeroDivisors A ≤ Submonoid.comap (algebraMap A B) (nonZeroDivisors B))

/- Clause (4): condition (4) implies condition (3). -/
#check (And.left :
  ((∀ q : PrimeSpectrum B, q.asIdeal ∈ associatedPrimes B B →
      (algebraMap A (Localization.AtPrime q.asIdeal)).Flat) ∧
    (∀ q : PrimeSpectrum B, q.asIdeal.under A ∈ associatedPrimes A A →
      (algebraMap A (Localization.AtPrime q.asIdeal)).Flat)) →
  ∀ q : PrimeSpectrum B, q.asIdeal ∈ associatedPrimes B B →
    (algebraMap A (Localization.AtPrime q.asIdeal)).Flat)

/- Lemma 49.14.1 (5): under going up, conditions (2) and (4) are equivalent. -/
@[stacks 0BWL]
#check (RingHom.Flat.totalQuotientBaseChange_iff_overAssociatedPrimes_of_goingUp :
  SpecializingMap (PrimeSpectrum.comap (algebraMap A B)) →
  ((nonZeroDivisors A ≤ Submonoid.comap (algebraMap A B) (nonZeroDivisors B) ∧
      (Algebra.TensorProduct.includeLeft :
        FractionRing A →ₐ[A] FractionRing A ⊗[A] B).toRingHom.Flat) ↔
    (∀ q : PrimeSpectrum B, q.asIdeal ∈ associatedPrimes B B →
        (algebraMap A (Localization.AtPrime q.asIdeal)).Flat) ∧
      (∀ q : PrimeSpectrum B, q.asIdeal.under A ∈ associatedPrimes A A →
        (algebraMap A (Localization.AtPrime q.asIdeal)).Flat)))

end RingHom.Flat
