/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
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
