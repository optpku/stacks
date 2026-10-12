/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Sequential Postnikov Towers

This leaf owns the intrinsic data of a sequential Postnikov tower. Finite reversed rows and
finite Postnikov-system restrictions are developed separately in `Tower.Finite`.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

variable (D) in
/-- Stacks 0D8Z: a sequential Postnikov tower consists of rows `Xₙ₊₁ ⟶ Xₙ`, auxiliary objects
`Yₙ`, and compatible distinguished triangles `Yₙ₊₁ ⟶ Xₙ₊₁ ⟶ Yₙ ⟶ Yₙ₊₁[1]`. -/
@[stacks 0D8Z "sequential Postnikov tower"]
structure Tower where
  /-- Objects of the underlying sequential row, written in decreasing direction. -/
  X : ℕ → D
  /-- The differential `Xₙ₊₁ ⟶ Xₙ`. -/
  d (n : ℕ) : X (n + 1) ⟶ X n
  /-- Auxiliary objects of the tower. -/
  Y : ℕ → D
  /-- The comparison `Yₙ ⟶ Xₙ`. -/
  toX (n : ℕ) : Y n ⟶ X n
  /-- The second map `Xₙ₊₁ ⟶ Yₙ` of a stage triangle. -/
  toNext (n : ℕ) : X (n + 1) ⟶ Y n
  /-- The connecting map `Yₙ ⟶ Yₙ₊₁[1]` of a stage triangle. -/
  connecting (n : ℕ) : Y n ⟶ (Y (n + 1))⟦(1 : ℤ)⟧
  /-- The right-end comparison `Y₀ ⟶ X₀` is invertible. -/
  base : IsIso (toX 0)
  /-- Every stage triangle is distinguished. -/
  distinguished (n : ℕ) :
    Triangle.mk (toX (n + 1)) (toNext n) (connecting n) ∈ distTriang D
  /-- The stage factorization recovers the differential `Xₙ₊₁ ⟶ Xₙ`. -/
  comp (n : ℕ) : toNext n ≫ toX n = d n

namespace Tower

/-- The base comparison of a sequential Postnikov tower is canonically an isomorphism. -/
instance toX_zero_isIso (T : Tower D) : IsIso (T.toX 0) :=
  T.base

/-- Consecutive differentials of a sequential Postnikov tower compose to zero. -/
@[reassoc]
theorem d_comp (T : Tower D) (n : ℕ) :
    T.d (n + 1) ≫ T.d n = 0 := sorry

end Tower
end CategoryTheory.PostnikovSystem
