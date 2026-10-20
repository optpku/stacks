module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Morphism.IsLevelwiseIso.Basic
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Morphism.Triangle

/-!
# Stage-Triangle Invertibility of Postnikov-System Morphisms

This leaf derives invertibility of every stage-triangle morphism of a
levelwise-invertible finite Postnikov-system morphism.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem.Morphism.IsLevelwiseIso

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D]

/-- Every stage-triangle morphism of a levelwise Postnikov-system isomorphism is invertible. -/
@[stacks 0D83]
theorem triangleMorphism {n : ℕ} {X X' : ComposableArrows D n} {P : PostnikovSystem X}
    {P' : PostnikovSystem X'} {φ : X ⟶ X'} {ψ : PostnikovSystem.Morphism P P' φ}
    (hψ : ψ.IsLevelwiseIso) (i : Fin n) :
    IsIso (ψ.triangleMorphism i) := sorry

end CategoryTheory.PostnikovSystem.Morphism.IsLevelwiseIso
