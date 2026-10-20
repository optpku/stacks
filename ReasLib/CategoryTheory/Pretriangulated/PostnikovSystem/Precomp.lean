/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.ComposableArrows.ZeroPrecomp
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Recursive
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Precomposition of Finite Postnikov Rows

This leaf owns the behavior of finite Postnikov-system existence and row
complexness under left precomposition. It keeps the row operation in the
canonical `ComposableArrows` API rather than introducing a second padded-row
representation.
-/

open scoped ZeroObject

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D]

namespace PostnikovSystem

/-- A Postnikov system on a left-precomposed row restricts to one on the original row. -/
@[stacks 0D81]
theorem nonempty_of_precomp {n : ℕ} {X : ComposableArrows D n} {Y : D}
    (f : Y ⟶ X.left) :
    Nonempty (PostnikovSystem (X.precomp f)) → Nonempty (PostnikovSystem X) := sorry

/-- If a row has no Postnikov system, no single left precomposition has a Postnikov system. -/
@[stacks 0D81]
theorem not_nonempty_precomp {n : ℕ} {X : ComposableArrows D n} {Y : D}
    (f : Y ⟶ X.left) (hX : ¬ Nonempty (PostnikovSystem X)) :
    ¬ Nonempty (PostnikovSystem (X.precomp f)) := sorry

/-- If a row has no Postnikov system, zero precomposition also has no Postnikov system. -/
@[stacks 0D81]
theorem not_nonempty_precomp_zero {n : ℕ} {X : ComposableArrows D n}
    (hX : ¬ Nonempty (PostnikovSystem X)) :
    ¬ Nonempty (PostnikovSystem (X.precomp (0 : (0 : D) ⟶ X.left))) := sorry

/-- Restrict a Postnikov system through a finite string of zero precompositions. -/
@[stacks 0D81]
noncomputable def ofZeroPrecomp {n : ℕ} (X : ComposableArrows D n) :
    (m : ℕ) → PostnikovSystem (X.zeroPrecomp m) → PostnikovSystem X
  | 0, P => P
  | m + 1, P => ofZeroPrecomp X m P.tail

/-- Restricting through zero zero-precompositions leaves the Postnikov system unchanged. -/
@[simp, stacks 0D81]
theorem ofZeroPrecomp_zero {n : ℕ} (X : ComposableArrows D n)
    (P : PostnikovSystem (X.zeroPrecomp 0)) :
    ofZeroPrecomp X 0 P = P := sorry

/-- Restriction through a successor zero-precomposition first removes its leftmost stage. -/
@[simp, stacks 0D81]
theorem ofZeroPrecomp_succ {n : ℕ} (X : ComposableArrows D n) (m : ℕ)
    (P : PostnikovSystem (X.zeroPrecomp (m + 1))) :
    ofZeroPrecomp X (m + 1) P = ofZeroPrecomp X m P.tail := sorry

/-- A Postnikov system on a zero-precomposed row restricts to one on the original row. -/
@[stacks 0D81]
theorem nonempty_of_zeroPrecomp {n : ℕ} (X : ComposableArrows D n) (m : ℕ) :
    Nonempty (PostnikovSystem (X.zeroPrecomp m)) → Nonempty (PostnikovSystem X) := sorry

/-- If a row has no Postnikov system, zero precomposition by any finite number of arrows also has
no Postnikov system. -/
@[stacks 0D81]
theorem not_nonempty_zeroPrecomp {n : ℕ} {X : ComposableArrows D n}
    (hX : ¬ Nonempty (PostnikovSystem X)) (m : ℕ) :
    ¬ Nonempty (PostnikovSystem (X.zeroPrecomp m)) := sorry

end PostnikovSystem

end

end CategoryTheory
