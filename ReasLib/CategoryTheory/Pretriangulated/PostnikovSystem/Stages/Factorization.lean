/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Stages.Maps

/-!
# Factorizations in Finite Postnikov Systems

This leaf records that the structural maps at every stage recover the
corresponding arrow of the underlying finite row.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.PostnikovSystem

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- The second and first comparison maps at a stage compose to the row differential. -/
@[reassoc, stacks 0D7Z]
theorem toNext_toX {n : ℕ} {X : ComposableArrows D n} (P : PostnikovSystem X) (i : Fin n) :
    P.toNext i ≫ P.toX i.succ = X.map' i.1 i.1.succ := sorry

attribute [simp] PostnikovSystem.toNext_toX_assoc

end CategoryTheory.PostnikovSystem
