/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Total.Forget
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Total.Tail.Basic

/-!
# Forgetful Coherence for Tails of Total Postnikov Systems

This leaf records compatibility between truncating a total finite Postnikov
system and forgetting to its underlying finite row.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem.Total

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ k : ℤ, Functor.Additive (shiftFunctor D k)] [Pretriangulated D]

variable (D) in
/-- Forgetting after total truncation agrees with truncating the underlying finite row. -/
@[stacks 0D7Z "tail compatibility with the underlying finite row"]
theorem tail_comp_forget (n : ℕ) :
    tail D n ⋙ forget D n =
      forget D (n + 1) ⋙ ComposableArrows.δ₀Functor (C := D) (n := n) := sorry

end CategoryTheory.PostnikovSystem.Total
