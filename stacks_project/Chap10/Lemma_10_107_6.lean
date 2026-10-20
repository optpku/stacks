/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.Epi
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.107.6

@stack 04VT
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.107.6: a ring map is surjective if and only if it is both an epimorphism and finite.
This is exactly the canonical theorem `RingHom.surjective_iff_epi_and_finite` in
`CommRingCat`. -/
@[stacks 04VT]
#check @RingHom.surjective_iff_epi_and_finite
