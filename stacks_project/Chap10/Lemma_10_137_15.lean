/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Smooth.AtPrime.Jacobian
import StacksCheckRecall

/-! @stack 00TE -/

@[expose] public section

/- Lemma 10.137.15, tag `00TE`: specialize the canonical Jacobian criterion
below to `P := Presentation.naive` for a presentation
`R[x₁, ..., xₙ] / (f₁, ..., f_c)`.  The first form uses mathlib's
`IsSmoothAt`; the second uses the equivalent Stacks-style primewise predicate. -/
@[stacks 00TE "IsSmoothAt Jacobian criterion"]
#check @Algebra.Presentation.IsRelativeGlobalCompleteIntersection.Jacobian.isSmoothAt_iff_exists_minor_not_mem

@[stacks 00TE "SmoothAtPrime Jacobian criterion"]
#check @Algebra.Presentation.IsRelativeGlobalCompleteIntersection.Jacobian.smoothAtPrime_iff_exists_minor_not_mem
