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
Lemma 9.7.5 (Tag 0BU1) is recalled through the canonical
`Algebra.EssFiniteType k (RatFunc k)` instance.
-/

universe u

section

variable (k : Type u) [Field k]

#synth Algebra.EssFiniteType k (RatFunc k)
@[stacks 0BU1]
#check RatFunc.not_finiteDimensional

end
