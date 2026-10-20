/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Perfect-field Frobenius criteria

@stack 030Z

The Frobenius formulation is the reusable owner-level interface.  The
characteristic-zero/positive-characteristic split is retained as a thin
source-facing companion with an ordinary natural-number prime, rather than a
subtype carrying repeated projections.
-/

@[expose] public section

universe u

namespace PerfectField

variable {K : Type u} [Field K]

/-- A field is perfect exactly when its Frobenius at the exponential characteristic is surjective.
The characteristic-zero case is represented uniformly by `ringExpChar K = 1`. -/
@[stacks 030Z "canonical Frobenius criterion"]
theorem iff_surjective_frobenius :
    PerfectField K ↔ Function.Surjective (frobenius K (ringExpChar K)) := sorry

/-- Definition 10.45.2 (Tag 030Z): a field is perfect exactly when it has characteristic zero or
has a prime positive characteristic whose Frobenius is surjective. -/
@[stacks 030Z]
theorem iff_charZero_or_exists_pthRoot :
    PerfectField K ↔
      CharZero K ∨
        ∃ p : ℕ, p.Prime ∧ CharP K p ∧
          ∀ x : K, ∃ y : K, y ^ p = x := sorry

end PerfectField
