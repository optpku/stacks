/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Localization.Away.Basic

@[expose] public section

namespace Localization.Away

/-- There is no ring homomorphism from `Localization.Away (2 : ℤ)` to `ℤ`. -/
theorem not_nonempty_ringHom_int_two :
    ¬ Nonempty (Localization.Away (2 : ℤ) →+* ℤ) := sorry

end Localization.Away
