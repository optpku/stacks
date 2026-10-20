/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.RingTheory.LocalRing.DimensionOne.FractionalIdealLength

open scoped BigOperators

universe u v

/- The containment assertion accompanying the length identity. -/
#check (Module.fractionIdeal_smul_le :
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (a b : A) (hdim : ringKrullDim A = 1)
    (ha : a ∈ nonZeroDivisors A) (hb : b ∈ nonZeroDivisors A)
    (hA : embeddedPrimes A = ∅)
    (hM : embeddedAssociatedPrimes A M = ∅)
    (hsupport : Module.support A M = Set.univ),
    (Ideal.span {a} * (Ideal.span {b}).colon (Ideal.span {a})) •
        (⊤ : Submodule A M) ≤
      Ideal.span {b} • (⊤ : Submodule A M))

/- Lemma 42.69.5: the length formula for a fraction and its denominator ideal. -/
@[stacks 02QH] #check (Module.length_fractionIdeal_quotient_sub_eq_sum :
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
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
      p.asIdeal ∈ minimalPrimes A → ∃ i, q i = p),
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
          (Ideal.Quotient.mk (q i).asIdeal b)).toNat : ℤ)))
