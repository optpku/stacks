/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.CrossRefAttribute

/-!
# The largest henselian ideal

The henselian ideals of a commutative ring form a set with a canonical greatest element.  The
underlying ideal is exposed as a concrete supremum; the henselianity and maximality laws are
separate proposition-valued declarations for downstream use.

@stack 0G1S
-/

@[expose] public section

universe u

variable {A : Type u} [CommRing A]

/-- The supremum of all ideals `I` for which `(A, I)` is a henselian pair. -/
@[stacks 0G1S "largest henselian ideal"]
def largestHenselianIdeal : Ideal A :=
  sSup {I : Ideal A | HenselianRing A I}

/-- The supremum defining `largestHenselianIdeal` is itself henselian. -/
@[stacks 0G1S "henselian structure for the largest henselian ideal"]
instance largestHenselianIdeal_henselianRing :
    HenselianRing A largestHenselianIdeal := sorry

/-- Every henselian ideal is contained in `largestHenselianIdeal`. -/
theorem le_largestHenselianIdeal (I : Ideal A) [HenselianRing A I] :
    I ≤ largestHenselianIdeal := sorry

/-- `largestHenselianIdeal` is the greatest member of the henselian ideals of `A`. -/
theorem isGreatest_largestHenselianIdeal :
    IsGreatest {I : Ideal A | HenselianRing A I} largestHenselianIdeal := sorry

/-- Lemma 15.11.15 (0G1S): every commutative ring has a largest ideal defining a henselian
pair. -/
@[stacks 0G1S "largest henselian ideal"]
theorem exists_largest_henselianIdeal :
    ∃ I : Ideal A, HenselianRing A I ∧ ∀ J : Ideal A, HenselianRing A J → J ≤ I := sorry
