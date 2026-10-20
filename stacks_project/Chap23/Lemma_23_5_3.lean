module

public import ReasLib.RingTheory.DividedPowers.Prime.Characterization
import StacksCheckRecall

@[expose] public section

open DividedPowers

universe u

section Uniqueness

variable {A : Type u} [CommRing A]
variable (p : ℕ) [Fact p.Prime] (I : Ideal A)
variable (hunit : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A))
variable {gamma delta : DividedPowers I}

/- Lemma 23.5.3 (1) (07GS): under the prime-to-`p` unit hypothesis, a divided power structure is
determined by its `p`th divided-power map. -/
@[stacks 07GS "(1)"]
#check (Ideal.dividedPowers_eq_iff_dpowPrime_eq p I hunit :
  gamma = delta ↔ gamma.dpowPrime p = delta.dpowPrime p)

end Uniqueness

section Existence

variable {A : Type u} [CommRing A]
variable (p : ℕ) [Fact p.Prime] (I : Ideal A)
variable (hunit : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) (delta : I → I)
variable (hfactorial : ∀ x : I, ((Nat.factorial p : A) * (delta x : A)) = (x : A) ^ p)
variable (hsmul : ∀ (a : A) (x : I), delta (a • x) = a ^ p • delta x)
variable (hadd : ∀ x y : I,
  (delta (x + y) : A) =
    (delta x : A) + dpowPrimeAddCorrection p x y + delta y)

/- Lemma 23.5.3 (2) (07GS): a map satisfying the prime divided-power identities extends uniquely
to a divided power structure. -/
@[stacks 07GS "(2)"]
#check (Ideal.existsUnique_dividedPowers_of_dpowPrime
    p I hunit delta hfactorial hsmul hadd :
  ∃! gamma : DividedPowers I, gamma.dpowPrime p = delta)

end Existence

#check @Function.IsDpowPrime
#check @Ideal.existsUnique_dividedPowers_of_isDpowPrime
