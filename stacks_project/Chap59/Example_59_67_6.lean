/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.IsAlgClosed.Cr
import StacksCheckRecall

@[expose] public section

universe u

namespace Field

/- Example 59.67.6: an algebraically closed field is `C_r` for every `r : ℕ`. -/
@[stacks 03RA] #check (Field.isCr_of_isAlgClosed :
  ∀ {K : Type u} [Field K] [IsAlgClosed K] (r : ℕ), Field.IsCr K r)

end Field
