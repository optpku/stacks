/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Total.Stage.Triangle
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.Functor.Basic
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.Stage.Triangle

/-!
# Evaluation of Finite Restrictions of Postnikov Towers

This leaf compares evaluation after finite restriction with the corresponding
row, auxiliary-object, and triangle evaluation functors on sequential towers.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem.Tower

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ k : ℤ, Functor.Additive (shiftFunctor D k)] [Pretriangulated D]

variable (D) in
/-- Finite-row restriction followed by position evaluation is evaluation of the original tower
at the corresponding tower index. -/
@[stacks 0D8Z "evaluation of a finite Postnikov-tower row"]
theorem rowFunctor_comp_eval (n : ℕ) (i : Fin (n + 1)) :
    rowFunctor D n ⋙ (evaluation (Fin (n + 1)) D).obj i =
      Stage.row D (Finite.index i) := sorry

variable (D) in
/-- Total finite restriction followed by row evaluation is row-object evaluation of the
original tower at the corresponding index. -/
@[stacks 0D8Z "row evaluation of finite Postnikov-tower restriction"]
theorem finiteFunctor_comp_row (n : ℕ) (i : Fin (n + 1)) :
    finiteFunctor D n ⋙ PostnikovSystem.Total.row D n i =
      Stage.row D (Finite.index i) := sorry

variable (D) in
/-- Total finite restriction followed by auxiliary evaluation is auxiliary-object evaluation of
the original tower at the corresponding index. -/
@[stacks 0D8Z "auxiliary evaluation of finite Postnikov-tower restriction"]
theorem finiteFunctor_comp_aux (n : ℕ) (i : Fin (n + 1)) :
    finiteFunctor D n ⋙ PostnikovSystem.Total.aux D n i =
      Stage.aux D (Finite.index i) := sorry

variable (D) in
/-- Total finite restriction followed by stage-triangle evaluation is stage evaluation of the
original tower at the corresponding differential index. -/
@[stacks 0D8Z "triangle evaluation of finite Postnikov-tower restriction"]
theorem finiteFunctor_comp_triangle (n : ℕ) (i : Fin n) :
    finiteFunctor D n ⋙ PostnikovSystem.Total.triangle D n i =
      Stage.triangle D (Finite.index i) := sorry

end CategoryTheory.PostnikovSystem.Tower
