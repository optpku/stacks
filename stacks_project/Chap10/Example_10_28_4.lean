/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.Oka.FiniteGeneration
import StacksCheckRecall

@[expose] public section

/-!
# Example 10.28.4
@stack 05KB
-/

/- Example 10.28.4 (1): the explicit finite-generator calculation. -/
@[stacks 05KB "explicit generator calculation"]
#check @Ideal.eq_span_mul_image_union_of_colon_sup_eq

/- Example 10.28.4 (2): finitely generated ideals form an Oka family. -/
@[stacks 05KB "finitely generated ideals form an Oka family"]
#check @Ideal.isOka_fg
