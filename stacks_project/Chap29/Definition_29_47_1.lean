module

import StacksCheckRecall
import ReasLib.RingTheory.Seminormal

universe u

variable (A : Type u) [CommRing A]

/- Definition 29.47.1 (1): seminormal rings. -/
@[stacks 0EUL] #check (SeminormalRing A : Prop)

#check (seminormalRing_iff A :
  SeminormalRing A ↔
    ∀ ⦃x y : A⦄, x ^ 3 = y ^ 2 → ∃! a : A, x = a ^ 2 ∧ y = a ^ 3)

/- Definition 29.47.1 (2): absolutely weakly normal rings. -/
@[stacks 0EUL] #check (AbsolutelyWeaklyNormalRing A : Prop)

#check (absolutelyWeaklyNormalRing_iff A :
  AbsolutelyWeaklyNormalRing A ↔
    SeminormalRing A ∧
      ∀ ⦃p : ℕ⦄, Nat.Prime p →
        ∀ ⦃x y : A⦄, ((p : A) ^ p) * x = y ^ p →
          ∃! a : A, x = a ^ p ∧ y = (p : A) * a)
