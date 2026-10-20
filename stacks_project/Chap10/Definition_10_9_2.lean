/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.GroupTheory.MonoidLocalization.Basic
public import Mathlib.RingTheory.Localization.Defs
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.9.2

@stack 00CO
-/

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (A : Type u) [CommRing A] (S : Submonoid A)

/- Definition 10.9.2: for a commutative ring `A` and a submonoid `S`, the canonical ring
`Localization S` is the localization of `A` with respect to `S`. -/
@[stacks 00CO "localization owner"]
#check @Localization

/- Companion recall: the owner abstraction for the statement that `Localization S` is the
localization of `A` with respect to `S` is the canonical instance
`Localization.isLocalization : IsLocalization S (Localization S)`. -/
@[stacks 00CO "localization universal property"]
#check @Localization.isLocalization

/- Companion recall: the natural localization map `A → Localization S`, sending `x` to `x / 1`,
is the canonical ring homomorphism `algebraMap A (Localization S)`, characterized by
`Localization.mk_one_eq_algebraMap`. -/
@[stacks 00CO "localization map"]
#check @Localization.mk_one_eq_algebraMap

end
