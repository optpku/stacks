/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Morphism.IsLevelwiseIso.Triangle

/-!
# Base Invertibility of Levelwise Postnikov-System Isomorphisms

This leaf derives invertibility of the underlying finite row of a
levelwise-invertible Postnikov-system morphism.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem.Morphism.IsLevelwiseIso

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D]

/-- Levelwise invertibility on auxiliary objects forces the underlying finite-row morphism to
be invertible. -/
@[stacks 0D83 "underlying row isomorphism of a levelwise Postnikov-system isomorphism"]
theorem base {n : ℕ} {X X' : ComposableArrows D n} {P : PostnikovSystem X}
    {P' : PostnikovSystem X'} {φ : X ⟶ X'} {ψ : PostnikovSystem.Morphism P P' φ}
    (hψ : ψ.IsLevelwiseIso) : IsIso φ := sorry

end CategoryTheory.PostnikovSystem.Morphism.IsLevelwiseIso
