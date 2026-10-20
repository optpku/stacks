/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.96.2

@stack 0317
-/

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]

/- Definition 10.96.2: an `R`-module `M` is `I`-adically complete if it satisfies the canonical
mathlib predicate `IsAdicComplete I M`; for `M = R`, this is the textbook notion that `R` is
`I`-adically complete as a ring. -/
@[stacks 0317 "adic completeness predicate"]
#check @IsAdicComplete

/- Companion recall: `AdicCompletion.of_bijective_iff` identifies `I`-adic completeness with the
statement that the canonical map `M → AdicCompletion I M`, i.e. to the inverse limit of the
quotients `M / I^n M`, is bijective. -/
@[stacks 0317 "adic completion comparison"]
#check @AdicCompletion.of_bijective_iff

end
