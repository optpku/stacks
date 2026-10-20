/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Recursive.Computation
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Indexed Objects of Finite Postnikov Systems

This leaf exposes the auxiliary-object family and its comparisons to the
underlying finite row, together with their recursive computations.
-/

@[expose] public section

open CategoryTheory.ComposableArrows
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.PostnikovSystem

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]
variable {n : ℕ} {X : ComposableArrows D n}

/-- The auxiliary object at a stage of a Postnikov system. -/
@[reducible, stacks 0D7Z]
def Y {n : ℕ} {X : ComposableArrows D n} (P : PostnikovSystem X) (i : Fin (n + 1)) : D :=
  match n, X, P, i with
  | 0, _, P, _ => P.head
  | _ + 1, _, P, ⟨0, _⟩ => P.head
  | _ + 1, _, P, ⟨i + 1, hi⟩ => P.tail.Y ⟨i, Nat.lt_of_succ_lt_succ hi⟩

/-- The zeroth auxiliary object of a nonzero Postnikov system is its head. -/
@[simp, stacks 0D7Z]
theorem Y_zero {n : ℕ} {X : ComposableArrows D (n + 1)} (P : PostnikovSystem X) :
    P.Y 0 = P.head := sorry

/-- Successor auxiliary objects are inherited from the tail Postnikov system. -/
@[simp, stacks 0D7Z]
theorem Y_succ {n : ℕ} {X : ComposableArrows D (n + 1)} (P : PostnikovSystem X)
    (i : Fin (n + 1)) :
    P.Y i.succ = P.tail.Y i := sorry

/-- The first successor auxiliary object is the head of the tail Postnikov system. -/
@[simp, stacks 0D7Z]
theorem Y_one {n : ℕ} {X : ComposableArrows D (n + 1)} (P : PostnikovSystem X) :
    P.Y 1 = P.tail.head := sorry

/-- The first successor auxiliary object is the tail head, in `Fin.succ` notation. -/
@[simp, stacks 0D7Z]
theorem Y_succZero {n : ℕ} {X : ComposableArrows D (n + 1)} (P : PostnikovSystem X) :
    P.Y (Fin.succ 0) = P.tail.head := sorry

/-- The zero auxiliary object is the head, in `Fin.castSucc` notation. -/
@[simp, stacks 0D7Z]
theorem Y_castSuccZero {n : ℕ} {X : ComposableArrows D (n + 1)}
    (P : PostnikovSystem X) :
    P.Y (Fin.castSucc 0) = P.head := sorry

/-- A Postnikov system evaluates to its auxiliary object at a finite index. -/
instance instCoeFun : CoeFun (PostnikovSystem X) (fun _ ↦ Fin (n + 1) → D) where
  coe P := P.Y

/-- Evaluation through the function coercion is the indexed auxiliary-object family. -/
@[simp, stacks 0D7Z]
theorem coe_apply (P : PostnikovSystem X) (i : Fin (n + 1)) :
    P i = P.Y i := sorry

/-- The comparison morphism from the auxiliary object to the corresponding row object. -/
@[stacks 0D7Z]
def toX {n : ℕ} {X : ComposableArrows D n} (P : PostnikovSystem X) (i : Fin (n + 1)) :
    P i ⟶ X.obj i :=
  match n, X, P, i with
  | 0, _, P, ⟨0, _⟩ => P.headToX
  | _ + 1, _, P, ⟨0, _⟩ => P.headToX
  | _ + 1, _, P, ⟨i + 1, hi⟩ => P.tail.toX ⟨i, Nat.lt_of_succ_lt_succ hi⟩

/-- The zeroth comparison map is the comparison stored at the head. -/
@[simp, stacks 0D7Z]
theorem toX_zero {n : ℕ} {X : ComposableArrows D (n + 1)} (P : PostnikovSystem X) :
    P.toX 0 = P.headToX := sorry

/-- Successor comparison maps are inherited from the tail Postnikov system. -/
@[simp, stacks 0D7Z]
theorem toX_succ {n : ℕ} {X : ComposableArrows D (n + 1)} (P : PostnikovSystem X)
    (i : Fin (n + 1)) : P.toX i.succ = P.tail.toX i := sorry

/-- The comparison map at the terminal row position is an isomorphism. -/
@[stacks 0D7Z]
instance toX_last_isIso {n : ℕ} {X : ComposableArrows D n} (P : PostnikovSystem X) :
    IsIso (P.toX (Fin.last n)) := sorry

end CategoryTheory.PostnikovSystem
