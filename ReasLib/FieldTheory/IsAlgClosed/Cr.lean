/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.Cr
public import Mathlib.FieldTheory.IsAlgClosed.Basic

universe u

@[expose] public section

namespace Field

/-- Every algebraically closed field is `C_r` for each natural number `r`. -/
theorem isCr_of_isAlgClosed {K : Type u} [Field K] [IsAlgClosed K] (r : ℕ) :
    IsCr K r := sorry

end Field
