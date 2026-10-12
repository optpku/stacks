/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.HopkinsLevitzki
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.60.5

@stack 00KH
-/

/- Lemma 10.60.5: a commutative ring is Artinian if and only if it is Noetherian and has Krull
dimension at most `0`. This is the canonical mathlib theorem
`isArtinianRing_iff_isNoetherianRing_krullDimLE_zero`, which packages both textbook directions:
"Noetherian of dimension `0` implies Artinian" and "Artinian implies Noetherian of dimension
zero". -/
@[stacks 00KH]
#check @isArtinianRing_iff_isNoetherianRing_krullDimLE_zero
