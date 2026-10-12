/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Stages.Maps.Computation

/-!
# Stage Triangles of Finite Postnikov Systems

This leaf packages each indexed stage as a stable triangle and provides its
projection, recursion, and distinguishedness API.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.PostnikovSystem

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]
variable {n : ℕ} {X : ComposableArrows D n}

/-- The distinguished triangle associated to a stage of a Postnikov system. -/
@[stacks 0D7Z]
def triangle (P : PostnikovSystem X) (i : Fin n) : Triangle D :=
  Triangle.mk (P.toX i.castSucc) (P.toNext i) (P.connecting i)

/-- The first object of a stage triangle is the current auxiliary object. -/
@[simp, stacks 0D7Z]
theorem triangle_obj₁ (P : PostnikovSystem X) (i : Fin n) :
    (P.triangle i).obj₁ = P i.castSucc := sorry

/-- The second object of a stage triangle is the current row object. -/
@[simp, stacks 0D7Z]
theorem triangle_obj₂ (P : PostnikovSystem X) (i : Fin n) :
    (P.triangle i).obj₂ = X.obj i.castSucc := sorry

/-- The third object of a stage triangle is the next auxiliary object. -/
@[simp, stacks 0D7Z]
theorem triangle_obj₃ (P : PostnikovSystem X) (i : Fin n) :
    (P.triangle i).obj₃ = P i.succ := sorry

/-- The first morphism of a stage triangle is its comparison to the row. -/
@[simp, stacks 0D7Z]
theorem triangle_mor₁ (P : PostnikovSystem X) (i : Fin n) :
    (P.triangle i).mor₁ = P.toX i.castSucc := sorry

/-- The second morphism of a stage triangle is `toNext`. -/
@[simp, stacks 0D7Z]
theorem triangle_mor₂ (P : PostnikovSystem X) (i : Fin n) :
    (P.triangle i).mor₂ = P.toNext i := sorry

/-- The third morphism of a stage triangle is the connecting map. -/
@[simp, stacks 0D7Z]
theorem triangle_mor₃ (P : PostnikovSystem X) (i : Fin n) :
    (P.triangle i).mor₃ = P.connecting i := sorry

/-- The zeroth stage triangle is the distinguished triangle stored at the head. -/
@[simp, stacks 0D7Z]
theorem triangle_zero {n : ℕ} {X : ComposableArrows D (n + 1)} (P : PostnikovSystem X) :
    P.triangle 0 = Triangle.mk P.headToX P.headToNext P.headConnecting := sorry

/-- Successor stage triangles are inherited from the tail Postnikov system. -/
@[simp, stacks 0D7Z]
theorem triangle_succ {n : ℕ} {X : ComposableArrows D (n + 2)} (P : PostnikovSystem X)
    (i : Fin (n + 1)) :
    P.triangle i.succ = P.tail.triangle i := sorry

/-- The triangle view of every Postnikov stage is distinguished. -/
@[stacks 0D7Z]
theorem triangle_distinguished (P : PostnikovSystem X) (i : Fin n) :
    P.triangle i ∈ distTriang D := sorry

end CategoryTheory.PostnikovSystem
