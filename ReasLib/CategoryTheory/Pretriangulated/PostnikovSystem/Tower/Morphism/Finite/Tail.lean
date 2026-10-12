/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Morphism.Tail
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.Morphism.Finite.System

/-!
# Tail Compatibility of Finite Postnikov-Tower Restrictions

This leaf compares finite-system restriction at a successor length with the
restriction at the preceding length after taking the recursive tail.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.PostnikovSystem.Tower.Hom

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]
variable {T T' : Tower D}

/-- Taking the tail of a successor finite-system restriction recovers the preceding restriction,
after transporting its underlying row map along successor compatibility. -/
@[simp, stacks 0D8Z "successor compatibility of finite Postnikov-system morphisms"]
theorem finite_succ_tail (f : Hom T T') (n : ℕ) :
    PostnikovSystem.Morphism.changeBase (row_succ_δ₀ f n)
      (PostnikovSystem.Morphism.tail (finite f (n + 1))) = finite f n := sorry

end CategoryTheory.PostnikovSystem.Tower.Hom
