/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Flat.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Remark 10.12.13

@stack 00DJ
-/

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {R : Type*} [CommRing R]
variable {N : Type*} [AddCommGroup N] [Module R N]

/- Remark 10.12.13: an `R`-module `N` for which tensoring on the right preserves exact
sequences is called a flat `R`-module; the canonical predicate for this notion is
`Module.Flat R N`. -/
@[stacks 00DJ "flat module predicate"]
#check @Module.Flat

/- Companion recall: over a commutative ring, flatness is equivalent to exactness of tensoring on
the right by `N`; this is exactly the canonical theorem `Module.Flat.iff_rTensor_exact`. -/
@[stacks 00DJ "right tensor exactness"]
#check @Module.Flat.iff_rTensor_exact

end
