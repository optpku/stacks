/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.QuotientByIdeal.Projective.Lift
import StacksCheckRecall

/-!
# Lemma 10.77.5 recall

The reusable owner is `Module.Projective.exists_lift_of_isNilpotent`.  It records the projective
lifting theorem independently of a chosen free cover, lifted projector, or idempotent correction.

@stack 07LV
-/

@[expose] public section

/- Lemma 10.77.5 (07LV): a projective `R ⧸ I`-module lifts across a nilpotent two-sided ideal
`I` to a projective `R`-module with a quotient-ring-linear comparison. -/
@[stacks 07LV] #check @Module.Projective.exists_lift_of_isNilpotent
