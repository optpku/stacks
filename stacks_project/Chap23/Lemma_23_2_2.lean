module

import StacksCheckRecall
public import ReasLib.RingTheory.DividedPowers.TorsionFree

@[expose] public section

universe u

section Factorial

variable {A : Type u} [CommRing A] {I : Ideal A}
variable (hI : DividedPowers I) (n : ℕ+) (x : I)

/- Lemma 23.2.2 (1) (07GM): divided powers satisfy the factorial formula. -/
@[stacks 07GM "(1)"]
#check (DividedPowers.factorial_mul_dpowPos_eq_pow hI n x :
  ((n : ℕ).factorial : A) * (hI.dpowPos n x : A) = (x : A) ^ (n : ℕ))

end Factorial

section TorsionFree

variable {A : Type u} [CommRing A] [Module.IsTorsionFree ℤ A]
variable (I : Ideal A)

/- Lemma 23.2.2 (2) (07GM): an ideal in a `ℤ`-torsion-free ring carries at
most one divided-power structure. -/
@[stacks 07GM "(2)"]
#check (Ideal.dividedPowersSubsingleton I : Subsingleton (DividedPowers I))

variable (gamma : ℕ+ → I → I)

/- Lemma 23.2.2 (3) (07GM): the factorial identities characterize the unique
divided-power structure inducing a chosen family of operations. -/
@[stacks 07GM "(3)"]
#check (Ideal.existsUnique_dividedPowers_iff I gamma :
  (∃! hI : DividedPowers I,
      ∀ n : ℕ+, ∀ x : I, hI.dpowPos n x = gamma n x) ↔
    I.HasDividedPowerFormula gamma)

/- Lemma 23.2.2 (4) (07GM): divided powers exist exactly when a generating
set satisfies the factorial divisibility criterion. -/
@[stacks 07GM "(4)"]
#check (Ideal.nonempty_dividedPowers_iff I :
  Nonempty (DividedPowers I) ↔ I.HasDividedPowerGenerators)

end TorsionFree

#check @Ideal.instSubsingletonDividedPowers
#check @Ideal.exists_dividedPowers_iff
