/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Cover
import StacksCheckRecall

/-!
# Remark 29.11.4

Detecting affine morphisms on an affine open cover.

@stack 01S9
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Remark 29.11.4: An affine-open cover of the target with affine pullbacks implies that the
morphism is affine. -/
@[stacks 01S9] #check
  (@AlgebraicGeometry.isAffineHom_of_affineOpenCover :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (𝒰 : S.AffineOpenCover),
      (∀ i : 𝒰.I₀, IsAffine ((𝒰.openCover.pullback₁ f).X i)) → IsAffineHom f)

/- Under the same affine-cover hypothesis, the inverse image of every affine open is affine. -/
#check
  (@AlgebraicGeometry.isAffineOpen_preimage_of_affineOpenCover :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (𝒰 : S.AffineOpenCover),
      (∀ i : 𝒰.I₀, IsAffine ((𝒰.openCover.pullback₁ f).X i)) →
        ∀ V : S.affineOpens, IsAffineOpen (f ⁻¹ᵁ (V : S.Opens)))
