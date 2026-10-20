module

public import Mathlib.RingTheory.DividedPowers.Basic
import StacksCheckRecall

@[expose] public section

universe u

variable {A : Type u} [CommSemiring A] (I : Ideal A)

/- Definition 23.2.1 (07GL): a divided power structure on an ideal is the canonical Mathlib
structure `DividedPowers`. -/
@[stacks 07GL] #check (DividedPowers I : Type u)
