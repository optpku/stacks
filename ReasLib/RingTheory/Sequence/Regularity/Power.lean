/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Positive powers of regular sequences

@stack 07DV

Regularity is invariant under replacing each entry of a finite sequence by a positive power.
-/

universe u v

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Lemma 10.68.9: a sequence is regular if and only if any entrywise choice of positive powers
is regular. -/
@[stacks 07DV "positive powers preserve regular sequences"]
theorem isRegular_iff_isRegular_pow
    {rs : List R} {es : List ℕ}
    (hes : List.Forall₂ (fun (_ : R) e ↦ 0 < e) rs es) :
    IsRegular M rs ↔ IsRegular M (rs.zipWith (· ^ ·) es) := sorry

end RingTheory.Sequence
