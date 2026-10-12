/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Etale.Weakly
public import ReasLib.RingTheory.WeakDimension
import Mathlib.Tactic.CrossRefAttribute

/-!
# Weak dimension under weakly etale maps

Weak dimension does not increase along a weakly etale map.  The conclusion is kept as an
explicit proposition rather than a global instance because the source ring is not determined by
the target ring.

@stack 092E
-/

@[expose] public section

universe u v

variable (A : Type u) [CommRing A]
variable (B : Type v) [CommRing B] [Algebra A B]
variable (d : ℕ) [HasWeakDimensionLE A d]

/-- Lemma 15.105.4 (092E): weak dimension does not increase along a weakly etale ring map. -/
@[stacks 092E "weak dimension under weakly etale maps"]
theorem hasWeakDimensionLE_of_isWeaklyEtale
    (hAB : Algebra.WeaklyEtale A B) :
    HasWeakDimensionLE B d := sorry
