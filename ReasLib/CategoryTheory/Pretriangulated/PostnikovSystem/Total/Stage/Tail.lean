/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Total.Stage.Differential
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Total.Stage.Triangle
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Total.Tail.Basic

/-!
# Stage Triangles after Truncation

This leaf records that removing the first stage of a total finite Postnikov system shifts every
remaining stage-triangle index by one.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem.Total

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ k : ℤ, Functor.Additive (shiftFunctor D k)] [Pretriangulated D]

variable (D) in
/-- Truncation followed by stage-triangle evaluation is evaluation at the successor stage. -/
@[stacks 0D7Z "stage-triangle evaluation after Postnikov truncation"]
theorem tail_comp_triangle (n : ℕ) (i : Fin n) :
    tail D n ⋙ triangle D n i = triangle D (n + 1) i.succ := sorry

/-- The second structural map of a truncated stage triangle is the successor component of the
original stage triangle. -/
@[simp, stacks 0D7Z "second stage map after Postnikov truncation"]
theorem tail_toNext_app {n : ℕ} (i : Fin n) (P : Total D (n + 1)) :
    (toNext D n i).app ((tail D n).obj P) =
      (toNext D (n + 1) i.succ).app P := sorry

/-- The connecting map of a truncated stage triangle is the successor component of the original
stage triangle. -/
@[simp, stacks 0D7Z "stage connecting map after Postnikov truncation"]
theorem tail_connecting_app {n : ℕ} (i : Fin n) (P : Total D (n + 1)) :
    (connecting D n i).app ((tail D n).obj P) =
      (connecting D (n + 1) i.succ).app P := sorry

/-- The differential of a truncated finite row is the successor differential of the original
row. -/
@[simp, stacks 0D7Z "differential after Postnikov truncation"]
theorem tail_d_app {n : ℕ} (i : Fin n) (P : Total D (n + 1)) :
    (d D n i).app ((tail D n).obj P) =
      (d D (n + 1) i.succ).app P := sorry

end CategoryTheory.PostnikovSystem.Total
