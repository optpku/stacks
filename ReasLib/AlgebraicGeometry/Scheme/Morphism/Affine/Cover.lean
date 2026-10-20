/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Tactic.CrossRefAttribute

/-!
# Detecting affine morphisms on an affine open cover

A morphism of schemes is affine if the pullbacks of the members of an affine open cover of its
target are affine. Consequently, the inverse image of every affine open is affine.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- If the pullbacks of the members of an affine open cover are affine, then the morphism is
affine. -/
@[stacks 01S9]
theorem isAffineHom_of_affineOpenCover
    {X S : Scheme.{u}} (f : X ⟶ S) (𝒰 : S.AffineOpenCover)
    (h𝒰 : ∀ i : 𝒰.I₀, IsAffine ((𝒰.openCover.pullback₁ f).X i)) :
    IsAffineHom f := by
  apply HasAffineProperty.of_openCover (P := @IsAffineHom) 𝒰.openCover
  intro i
  exact h𝒰 i

/-- A morphism of schemes is affine if and only if the pullbacks of the members of some affine
open cover of its target are affine. -/
theorem isAffineHom_iff_exists_affineOpenCover
    {X S : Scheme.{u}} (f : X ⟶ S) :
    IsAffineHom f ↔
      ∃ 𝒰 : S.AffineOpenCover.{u},
        ∀ i : 𝒰.I₀, IsAffine ((𝒰.openCover.pullback₁ f).X i) := by
  constructor
  · intro hf
    refine ⟨S.affineOpenCover, ?_⟩
    exact
      (HasAffineProperty.iff_of_openCover (P := @IsAffineHom)
        S.affineOpenCover.openCover).mp hf
  · rintro ⟨𝒰, h𝒰⟩
    exact isAffineHom_of_affineOpenCover f 𝒰 h𝒰

/-- Under the affine-cover criterion, the inverse image of every affine open is affine. -/
@[stacks 01S9]
theorem isAffineOpen_preimage_of_affineOpenCover
    {X S : Scheme.{u}} (f : X ⟶ S) (𝒰 : S.AffineOpenCover)
    (h𝒰 : ∀ i : 𝒰.I₀, IsAffine ((𝒰.openCover.pullback₁ f).X i))
    (V : S.affineOpens) :
    IsAffineOpen (f ⁻¹ᵁ (V : S.Opens)) := by
  exact (isAffineHom_iff f).mp (isAffineHom_of_affineOpenCover f 𝒰 h𝒰) V V.2

end AlgebraicGeometry
