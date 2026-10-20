/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Stages.Basic
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.Finite.Construction
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.Finite.Index

/-!
# Objects of Finite Restrictions of Postnikov Towers

This leaf identifies the row and auxiliary objects of a finite restriction with
the corresponding objects of the sequential tower. It contains no structural-map
computations.
-/

@[expose] public section

open CategoryTheory.ComposableArrows
open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem.Tower

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- The left endpoint of `T.row n` is `Xₙ`. -/
@[simp, stacks 0D8Z]
theorem row_left (T : Tower D) (n : ℕ) :
    (T.row n).left = T.X n := sorry

/-- The head auxiliary object of the finite restriction is `Yₙ`. -/
@[simp, stacks 0D8Z]
theorem finite_head (T : Tower D) (n : ℕ) :
    (T.finite n).head = T.Y n := sorry

namespace Finite

/-- The object at a position of the reversed finite row is the corresponding tower object. -/
@[simp, stacks 0D8Z]
theorem rowObj (T : Tower D) (n : ℕ) (i : Fin (n + 1)) :
    (T.row n).obj i = T.X (index i) := sorry

/-- The auxiliary object at a position of the finite restriction is the corresponding tower
auxiliary object. -/
@[simp, stacks 0D8Z]
theorem auxObj (T : Tower D) (n : ℕ) (i : Fin (n + 1)) :
    T.finite n i = T.Y (index i) := sorry

/-- The source of a finite-row arrow is the successor object of its tower stage. -/
@[simp, stacks 0D8Z]
theorem rowSource (T : Tower D) (n : ℕ) (i : Fin n) :
    (T.row n).obj i.castSucc = T.X (index i + 1) := sorry

/-- The target of a finite-row arrow is the object of its tower stage. -/
@[simp, stacks 0D8Z]
theorem rowTarget (T : Tower D) (n : ℕ) (i : Fin n) :
    (T.row n).obj i.succ = T.X (index i) := sorry

/-- The auxiliary object at the source position of a finite-row arrow is the successor
auxiliary object of its tower stage. -/
@[simp, stacks 0D8Z]
theorem auxSource (T : Tower D) (n : ℕ) (i : Fin n) :
    T.finite n i.castSucc = T.Y (index i + 1) := sorry

/-- The auxiliary object at the target position of a finite-row arrow is the auxiliary object
of its tower stage. -/
@[simp, stacks 0D8Z]
theorem auxTarget (T : Tower D) (n : ℕ) (i : Fin n) :
    T.finite n i.succ = T.Y (index i) := sorry

end Finite

end CategoryTheory.PostnikovSystem.Tower
