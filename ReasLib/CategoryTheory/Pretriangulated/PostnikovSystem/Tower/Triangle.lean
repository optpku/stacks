/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.Basic

/-!
# Stage Triangles of Sequential Postnikov Towers

This leaf packages each stage of a sequential Postnikov tower as a triangle and
provides its projection, distinguishedness, and factorization API.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.PostnikovSystem.Tower

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- Stacks 0D8Z: the distinguished triangle associated to a stage of a sequential Postnikov
tower. -/
@[stacks 0D8Z "stage triangle of a sequential Postnikov tower"]
def triangle (T : Tower D) (n : ℕ) : Triangle D :=
  Triangle.mk (T.toX (n + 1)) (T.toNext n) (T.connecting n)

/-- The first object of a tower stage triangle is the next auxiliary object. -/
@[simp, stacks 0D8Z]
theorem triangle_obj₁ (T : Tower D) (n : ℕ) :
    (T.triangle n).obj₁ = T.Y (n + 1) := sorry

/-- The second object of a tower stage triangle is the next row object. -/
@[simp, stacks 0D8Z]
theorem triangle_obj₂ (T : Tower D) (n : ℕ) :
    (T.triangle n).obj₂ = T.X (n + 1) := sorry

/-- The third object of a tower stage triangle is the current auxiliary object. -/
@[simp, stacks 0D8Z]
theorem triangle_obj₃ (T : Tower D) (n : ℕ) :
    (T.triangle n).obj₃ = T.Y n := sorry

/-- The first morphism of a tower stage triangle is its comparison to the row. -/
@[simp, stacks 0D8Z]
theorem triangle_mor₁ (T : Tower D) (n : ℕ) :
    (T.triangle n).mor₁ = T.toX (n + 1) := sorry

/-- The second morphism of a tower stage triangle is `toNext`. -/
@[simp, stacks 0D8Z]
theorem triangle_mor₂ (T : Tower D) (n : ℕ) :
    (T.triangle n).mor₂ = T.toNext n := sorry

/-- The third morphism of a tower stage triangle is the connecting map. -/
@[simp, stacks 0D8Z]
theorem triangle_mor₃ (T : Tower D) (n : ℕ) :
    (T.triangle n).mor₃ = T.connecting n := sorry

/-- The triangle view of every sequential Postnikov-tower stage is distinguished. -/
@[stacks 0D8Z "distinguished stage triangle of a sequential Postnikov tower"]
theorem triangle_distinguished (T : Tower D) (n : ℕ) :
    T.triangle n ∈ distTriang D := sorry

/-- The two comparison maps at a tower stage compose to the tower differential. -/
@[reassoc, stacks 0D8Z "factorization of a sequential Postnikov-tower differential"]
theorem toNext_toX (T : Tower D) (n : ℕ) :
    T.toNext n ≫ T.toX n = T.d n := sorry

attribute [simp] Tower.toNext_toX_assoc

end CategoryTheory.PostnikovSystem.Tower
