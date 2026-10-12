/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.RatFunc.FiniteGeneration
import StacksCheckRecall

@[expose] public section

/-!
Example 9.7.4 (Degree of a rational function field, Tag 09G6) is the canonical fact that a
rational function field is not finite-dimensional over its coefficient field.
-/

@[stacks 09G6]
#check RatFunc.not_finiteDimensional
