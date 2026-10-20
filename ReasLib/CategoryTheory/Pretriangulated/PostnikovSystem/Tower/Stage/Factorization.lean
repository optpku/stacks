module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.Stage.Basic

/-!
# Stage Factorizations in Sequential Postnikov Towers

This leaf records the natural-transformation form of the factorization axiom relating each
stage triangle to the differential of a sequential Postnikov tower.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem.Tower.Stage

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ k : ℤ, Functor.Additive (shiftFunctor D k)] [Pretriangulated D]

variable (D) in
/-- At every tower stage, the second triangle map followed by the auxiliary-to-row comparison
is the corresponding tower differential. -/
@[stacks 0D8Z "factorization of a sequential Postnikov-tower differential"]
theorem toNext_comp_toX (n : ℕ) :
    toNext D n ≫ toX D n = d D n := sorry

end CategoryTheory.PostnikovSystem.Tower.Stage
