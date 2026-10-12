/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.IsIso.Basic
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.Morphism.Triangle

/-!
# Stage-Triangle Isomorphisms of Sequential Postnikov Towers

This leaf isolates the passage from levelwise invertibility of a tower morphism
to invertibility of each induced stage-triangle morphism.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem.Tower.Hom.IsLevelwiseIso

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]
variable {T T' : Tower D}

/-- A levelwise-invertible tower morphism induces an isomorphism at every stage triangle. -/
@[stacks 0D8Z]
theorem triangleMorphism {f : T ⟶ T'} (hf : f.IsLevelwiseIso) (n : ℕ) :
    IsIso (Hom.triangleMorphism f n) := sorry

end CategoryTheory.PostnikovSystem.Tower.Hom.IsLevelwiseIso
