/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.CentralSimple.BrauerGroup.Group
public import ReasLib.FieldTheory.Cr

@[expose] public section

universe u

namespace BrauerGroup

/-- Every Brauer class over a C₁ field is the neutral class. -/
theorem eq_one_of_isCr {K : Type u} [Field K] (hC1 : Field.IsCr K 1) (A : Br(K)) : A = 1 := sorry

end BrauerGroup

end
