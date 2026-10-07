module

public import ReasLib.RingTheory.CohenMacaulay.Module.Multiplicity
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Embedded
public import ReasLib.RingTheory.Ideal.Colon

@[expose] public section

open scoped BigOperators

universe u v

namespace Module

/-- For the denominator ideal `(b) : (a)`, multiplication by `a` sends its action on
`M` into the action of `(b)` on `M`. -/
theorem fractionIdeal_smul_le
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (a b : A) (hdim : ringKrullDim A = 1)
    (ha : a ∈ nonZeroDivisors A) (hb : b ∈ nonZeroDivisors A)
    (hA : embeddedPrimes A = ∅)
    (hM : embeddedAssociatedPrimes A M = ∅)
    (hsupport : Module.support A M = Set.univ) :
    (Ideal.span {a} * (Ideal.span {b}).colon (Ideal.span {a})) •
        (⊤ : Submodule A M) ≤
      Ideal.span {b} • (⊤ : Submodule A M) := sorry

/-- The difference between the lengths of the quotients of `M` by `(a) : (b)` and
`(b) : (a)` is the sum over the minimal primes of the generic lengths of `M`,
weighted by the corresponding differences of orders of `a` and `b`. -/
theorem length_fractionIdeal_quotient_sub_eq_sum
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (a b : A) (hdim : ringKrullDim A = 1)
    (ha : a ∈ nonZeroDivisors A) (hb : b ∈ nonZeroDivisors A)
    (hA : embeddedPrimes A = ∅)
    (hM : embeddedAssociatedPrimes A M = ∅)
    (hsupport : Module.support A M = Set.univ)
    {t : ℕ} (q : Fin t → PrimeSpectrum A)
    (hq_injective : Function.Injective q)
    (hq_minimal : ∀ i, (q i).asIdeal ∈ minimalPrimes A)
    (hq_complete : ∀ p : PrimeSpectrum A,
      p.asIdeal ∈ minimalPrimes A → ∃ i, q i = p) :
    ((Module.length A
      (M ⧸ ((Ideal.span {a}).colon (Ideal.span {b}) •
        (⊤ : Submodule A M)))).toNat : ℤ) -
      ((Module.length A
        (M ⧸ ((Ideal.span {b}).colon (Ideal.span {a}) •
          (⊤ : Submodule A M)))).toNat : ℤ) =
    ∑ i, ((Module.length (Localization.AtPrime (q i).asIdeal)
        (LocalizedModule.AtPrime (q i).asIdeal M)).toNat : ℤ) *
      (((Ring.ord (A ⧸ (q i).asIdeal)
          (Ideal.Quotient.mk (q i).asIdeal a)).toNat : ℤ) -
        ((Ring.ord (A ⧸ (q i).asIdeal)
          (Ideal.Quotient.mk (q i).asIdeal b)).toNat : ℤ)) := sorry

end Module
