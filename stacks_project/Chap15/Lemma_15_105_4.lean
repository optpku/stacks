/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.WeakDimension.WeaklyEtale
import StacksCheckRecall

/-!
Lemma 15.105.4 (092E): weak dimension does not increase along a weakly etale ring map.

@stack 092E
-/

@[expose] public section

universe u v

variable (A : Type u) [CommRing A]
variable (B : Type v) [CommRing B] [Algebra A B]
variable (d : ℕ) [HasWeakDimensionLE A d]

/- Lemma 15.105.4 (092E): if `A → B` is weakly etale and `A` has weak dimension at most
`d`, then `B` has weak dimension at most `d`. -/
@[stacks 092E]
#check
  (hasWeakDimensionLE_of_isWeaklyEtale A B d :
    Algebra.WeaklyEtale A B → HasWeakDimensionLE B d)
