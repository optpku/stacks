/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Stages.Basic
public import Mathlib.Combinatorics.Quiver.Cast

/-!
# Structural Maps of Finite Postnikov Stages

This leaf defines the second and connecting maps at each stage. Import
`Stages.Maps.Computation` for their zero and successor computation rules.
-/

@[expose] public section

open CategoryTheory.ComposableArrows
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.PostnikovSystem

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- The second map of the distinguished triangle at a stage of a Postnikov system. -/
@[stacks 0D7Z]
def toNext {n : ℕ} {X : ComposableArrows D n} (P : PostnikovSystem X) (i : Fin n) :
    X.obj i.castSucc ⟶ P i.succ :=
  match n, X, P, i with
  | 0, _, _, i => nomatch i
  | 1, _, P, ⟨0, _⟩ => P.headToNext.cast rfl rfl
  | _ + 2, _, P, ⟨0, _⟩ => P.headToNext.cast rfl rfl
  | _ + 2, _, P, ⟨i + 1, hi⟩ =>
      P.tail.toNext ⟨i, Nat.lt_of_succ_lt_succ hi⟩

/-- The connecting map of the distinguished triangle at a stage of a Postnikov system. -/
@[stacks 0D7Z]
def connecting {n : ℕ} {X : ComposableArrows D n} (P : PostnikovSystem X) (i : Fin n) :
    P i.succ ⟶ (P i.castSucc)⟦(1 : ℤ)⟧ :=
  match n, X, P, i with
  | 0, _, _, i => nomatch i
  | 1, _, P, ⟨0, _⟩ => P.headConnecting.cast rfl rfl
  | _ + 2, _, P, ⟨0, _⟩ => P.headConnecting.cast rfl rfl
  | _ + 2, _, P, ⟨i + 1, hi⟩ =>
      P.tail.connecting ⟨i, Nat.lt_of_succ_lt_succ hi⟩

end CategoryTheory.PostnikovSystem
