/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Recursive
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.Basic

/-!
# Finite Restrictions of Sequential Postnikov Towers

This leaf constructs the reversed finite rows and finite Postnikov systems of a
sequential tower. Positional computations and the complex property are separate.
-/

@[expose] public section

open CategoryTheory.ComposableArrows
open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem.Tower

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

namespace Core

/-- Internal row data retaining only the left-endpoint equality needed by the next
`ComposableArrows.precomp` step. -/
structure Row (T : Tower D) (n : ℕ) where
  /-- The reversed finite row `Xₙ ⟶ ⋯ ⟶ X₀`. -/
  val : ComposableArrows D n
  /-- Identification of the left endpoint with `Xₙ`. -/
  leftEq : val.left = T.X n

/-- The proof-clean recursion constructing all reversed finite rows of a tower. -/
def rows (T : Tower D) : (n : ℕ) → Row T n
  | 0 => ⟨ComposableArrows.mk₀ (T.X 0), rfl⟩
  | n + 1 =>
      let R := rows T n
      ⟨R.val.precomp (T.d n ≫ eqToHom R.leftEq.symm), rfl⟩

end Core

/-- Stacks 0D8Z: the reversed finite row `Xₙ ⟶ Xₙ₋₁ ⟶ ⋯ ⟶ X₀` cut out from a sequential
Postnikov tower. -/
@[stacks 0D8Z "finite row of a sequential Postnikov tower"]
def row (T : Tower D) (n : ℕ) : ComposableArrows D n :=
  (Core.rows T n).val

namespace Core

set_option linter.defProp false in
/-- The endpoint equality carried by the proof-clean finite-row recursion. -/
def rowLeftEq (T : Tower D) (n : ℕ) :
    (T.row n).left = T.X n :=
  (rows T n).leftEq

/-- Internal recursive data retaining the proof fields needed to extend a finite Postnikov
system by one stage. -/
structure Prefix (T : Tower D) (n : ℕ) where
  /-- The finite Postnikov system induced on the proof-clean row. -/
  system : PostnikovSystem (T.row n)
  /-- Identification of the head auxiliary object. -/
  headEq : system.head = T.Y n
  /-- Identification of the head comparison map. -/
  headToXEq :
    system.headToX = eqToHom headEq ≫ T.toX n ≫ eqToHom (rowLeftEq T n).symm

namespace Prefix

/-- The length-zero system used to start the finite-prefix recursion. -/
abbrev zeroSystem (T : Tower D) : PostnikovSystem (T.row 0) :=
  @PostnikovSystem.mk₀ D _ _ _ _ _ _ (T.row 0) (T.Y 0) (T.toX 0) T.base

/-- The head comparison of the length-zero system has the expected endpoint-normalized form. -/
theorem zero_headToXEq (T : Tower D) :
    (zeroSystem T).headToX =
      eqToHom (rfl : (zeroSystem T).head = T.Y 0) ≫ T.toX 0 ≫
        eqToHom (rowLeftEq T 0).symm := sorry

/-- The length-zero finite prefix of a sequential Postnikov tower. -/
def zero (T : Tower D) : Prefix T 0 where
  system := zeroSystem T
  headEq := rfl
  headToXEq := zero_headToXEq T

/-- The map from the new row object to the previous auxiliary object. -/
def nextToNext {T : Tower D} {n : ℕ} (P : Prefix T n) :
    (T.row (n + 1)).left ⟶ P.system.head :=
  T.toNext n ≫ eqToHom P.headEq.symm

/-- The connecting map from the previous auxiliary object to the shifted new one. -/
def nextConnecting {T : Tower D} {n : ℕ} (P : Prefix T n) :
    P.system.head ⟶ (T.Y (n + 1))⟦(1 : ℤ)⟧ :=
  eqToHom P.headEq ≫ T.connecting n

/-- Endpoint transport preserves distinguishedness of the next tower triangle. -/
theorem next_distinguished {T : Tower D} {n : ℕ} (P : Prefix T n) :
    Triangle.mk (T.toX (n + 1)) (nextToNext P) (nextConnecting P) ∈
      distTriang D := sorry

/-- The transported next-stage maps recover the first map of the extended finite row. -/
theorem next_comp {T : Tower D} {n : ℕ} (P : Prefix T n) :
    nextToNext P ≫ P.system.headToX = (T.row (n + 1)).map' 0 1 := sorry

/-- Extend a finite Postnikov system by the next stage of the tower. -/
abbrev nextSystem {T : Tower D} {n : ℕ} (P : Prefix T n) :
    PostnikovSystem (T.row (n + 1)) :=
  PostnikovSystem.mkSucc P.system (T.Y (n + 1)) (T.toX (n + 1))
    (nextToNext P) (nextConnecting P) (next_distinguished P) (next_comp P)

/-- The extended system has the expected endpoint-normalized head comparison. -/
theorem next_headToXEq {T : Tower D} {n : ℕ} (P : Prefix T n) :
    (nextSystem P).headToX =
      eqToHom (rfl : (nextSystem P).head = T.Y (n + 1)) ≫ T.toX (n + 1) ≫
        eqToHom (rowLeftEq T (n + 1)).symm := sorry

/-- Extend the complete finite-prefix package by one stage. -/
def succ {T : Tower D} {n : ℕ} (P : Prefix T n) : Prefix T (n + 1) where
  system := nextSystem P
  headEq := rfl
  headToXEq := next_headToXEq P

end Prefix

/-- The internal finite-system recursion associated to a sequential Postnikov tower. -/
def build (T : Tower D) : (n : ℕ) → Prefix T n
  | 0 => Prefix.zero T
  | n + 1 => Prefix.succ (build T n)

end Core

/-- Stacks 0D8Z: the finite Postnikov system canonically induced on `T.row n`. -/
@[stacks 0D8Z "finite restriction of a sequential Postnikov tower"]
def finite (T : Tower D) (n : ℕ) : PostnikovSystem (T.row n) :=
  (Core.build T n).system

end CategoryTheory.PostnikovSystem.Tower
