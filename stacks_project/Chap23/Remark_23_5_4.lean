/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DividedPowers.Prime.Characterization
import StacksCheckRecall

@[expose] public section

open Nat DividedPowers

universe u

section

variable {A : Type u} [CommRing A]
variable {p : ℕ} [Fact p.Prime]
variable (I : Ideal A)
variable (hunit : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : A))
variable (delta : I → I)
variable (hsmul : ∀ (a : A) (x : I), delta (a • x) = a ^ p • delta x)
variable (hadd : ∀ x y : I,
  (delta (x + y) : A) =
    (delta x : A) + dpowPrimeAddCorrection p x y + delta y)

/- Remark 23.5.4 (1) (0H87): the factorial identity follows from the scalar and addition laws for
a candidate prime divided-power operation. -/
@[stacks 0H87 "factorial identity"]
#check (Function.IsDpowPrime.factorial_of_smul_add I hunit delta hsmul hadd :
  ∀ x : I, (p ! : A) * (delta x : A) = (x : A) ^ p)

/- Remark 23.5.4 (2) (0H87): those two laws therefore assemble into the canonical bundled
predicate `Function.IsDpowPrime`. -/
@[stacks 0H87 "bundled constructor"]
#check (Function.IsDpowPrime.of_smul_add I hunit delta hsmul hadd :
  delta.IsDpowPrime p)

end
