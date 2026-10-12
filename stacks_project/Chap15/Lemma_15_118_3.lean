/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.PicardGroup
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.118.3

This is a direct canonical recall: Mathlib's Picard-group instance for a domain with a gcd
monoid already makes the Picard group of a UFD subsingleton.

@stack 0BCH
-/

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]

/- Lemma 15.118.3: a UFD has trivial Picard group. -/
@[stacks 0BCH "Lemma 15.118.3: a UFD has trivial Picard group"]
#check (inferInstance : Subsingleton (CommRing.Pic R))

end
