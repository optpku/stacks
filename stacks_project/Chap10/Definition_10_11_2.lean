/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section ModuleRelations

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {ι : Type w} [Fintype ι]

/-!
# Definition 10.11.2

@stack 07N8

The source definition is the canonical finite linear combination, so the chapter entry recalls
`Fintype.linearCombination` directly instead of introducing a parallel relation predicate.
-/
@[stacks 07N8]
#check @Fintype.linearCombination

end ModuleRelations
