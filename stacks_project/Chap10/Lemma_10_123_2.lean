/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.ZariskisMainTheorem
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.123.2 (Tag 00PT): a monic polynomial relation permits integral subtraction.

@stack 00PT
-/

/- Lemma 10.123.2, tag 00PT: after a monic polynomial relation, one may subtract an image
so that the remainder is integral over the coefficient ring. -/
@[stacks 00PT]
#check @exists_isIntegral_sub_of_isIntegralElem_of_mul_mem_range
