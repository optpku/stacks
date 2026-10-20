/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Flat.EquationalCriterion
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.39.11 (Equational criterion of flatness)

@stack 00HK
-/

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/- Lemma 10.39.11 (Equational criterion of flatness): an `R`-module `M` is flat if and only if
every relation in `M` is trivial. In mathlib, triviality of a finite relation
`∑ i, f i • x i = 0` is the predicate `Module.IsTrivialRelation f x`, and the canonical owner
theorem for this criterion is `Module.Flat.iff_forall_isTrivialRelation`. -/
@[stacks 00HK]
#check @Module.Flat.iff_forall_isTrivialRelation

end
