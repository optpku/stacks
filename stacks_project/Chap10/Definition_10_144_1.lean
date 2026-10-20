/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Etale.StandardEtale
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.144.1

@stack 00UB
-/

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/- Definition 10.144.1: the canonical notion that the ring map `R → S` is standard étale is
`IsStandardEtale R S`. The textbook's concrete presentation is the bridge object
`StandardEtalePresentation R S`, which extends a `StandardEtalePair R` by choosing the image of
`X` in `S` and an `R`-algebra identification of `S` with the associated standard étale algebra. -/
@[stacks 00UB "standard étale predicate"]
#check @IsStandardEtale

/- A `StandardEtalePresentation R S` is the source-facing bridge from the textbook polynomial data
to the intrinsic owner predicate `IsStandardEtale R S`. -/
@[stacks 00UB "standard étale presentation data"]
#check @StandardEtalePresentation

end Algebra
