/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Stages.Maps

/-!
# Computations for Structural Maps of Finite Postnikov Stages

This leaf exposes the zero and successor computations for the second and
connecting maps of an indexed Postnikov stage.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.PostnikovSystem

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- The second map at the zeroth stage is the second map stored at the head. -/
@[simp, stacks 0D7Z]
theorem toNext_zero {n : ℕ} {X : ComposableArrows D (n + 1)} (P : PostnikovSystem X) :
    P.toNext 0 = P.headToNext.cast rfl P.Y_succZero.symm := sorry

/-- Second maps at successor stages are inherited from the tail Postnikov system. -/
@[simp, stacks 0D7Z]
theorem toNext_succ {n : ℕ} {X : ComposableArrows D (n + 1)} (P : PostnikovSystem X)
    (i : Fin n) :
    P.toNext i.succ = P.tail.toNext i := sorry

/-- The connecting map at the zeroth stage is the connecting map stored at the head. -/
@[simp, stacks 0D7Z]
theorem connecting_zero {n : ℕ} {X : ComposableArrows D (n + 1)} (P : PostnikovSystem X) :
    P.connecting 0 = P.headConnecting.cast P.Y_succZero.symm
      (congrArg (shiftFunctor D (1 : ℤ)).obj P.Y_castSuccZero.symm) := sorry

/-- Connecting maps at successor stages are inherited from the tail Postnikov system. -/
@[simp, stacks 0D7Z]
theorem connecting_succ {n : ℕ} {X : ComposableArrows D (n + 1)} (P : PostnikovSystem X)
    (i : Fin n) :
    P.connecting i.succ = P.tail.connecting i := sorry

end CategoryTheory.PostnikovSystem
