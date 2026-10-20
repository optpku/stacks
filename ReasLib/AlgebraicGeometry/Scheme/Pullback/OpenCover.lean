/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Affine open covers of fibre products

This leaf packages the standard two-stage refinement of an affine open cover
of the base of a fibre product.  It is independent of any particular
application of the fibre product.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry
namespace Scheme.Pullback

universe u

variable {S X Y : Scheme.{u}}

/-- The open cover of `X ×_S Y` whose members are the fibre-product charts obtained from an
affine open cover of `S` and affine open covers of its inverse images in `X` and `Y`. -/
@[simps! I₀ X f, stacks 01JS "explicit affine-chart cover of a fibre product"]
def openCover
    (f : X ⟶ S) (g : Y ⟶ S) (𝒰 : S.AffineOpenCover)
    (𝒱 : ∀ i : 𝒰.I₀, ((𝒰.openCover.pullback₁ f).X i).AffineOpenCover)
    (𝒲 : ∀ i : 𝒰.I₀, ((𝒰.openCover.pullback₁ g).X i).AffineOpenCover) :
    (pullback f g).OpenCover :=
  (openCoverOfBase 𝒰.openCover f g).bind fun i ↦
    openCoverOfLeftRight
      (𝒱 i).openCover
      (𝒲 i).openCover
      (𝒰.openCover.pullbackHom f i)
      (𝒰.openCover.pullbackHom g i)

/-- Every member of `openCover f g 𝒰 𝒱 𝒲` is affine. -/
@[stacks 01JS]
instance openCover_isAffine
    (f : X ⟶ S) (g : Y ⟶ S) (𝒰 : S.AffineOpenCover)
    (𝒱 : ∀ i : 𝒰.I₀, ((𝒰.openCover.pullback₁ f).X i).AffineOpenCover)
    (𝒲 : ∀ i : 𝒰.I₀, ((𝒰.openCover.pullback₁ g).X i).AffineOpenCover)
    (I : (openCover f g 𝒰 𝒱 𝒲).I₀) :
    IsAffine ((openCover f g 𝒰 𝒱 𝒲).X I) := sorry

/-- Lemma 26.17.4: the affine open cover of `X ×_S Y` represented by the explicit fibre-product
charts in `openCover f g 𝒰 𝒱 𝒲`. -/
@[stacks 01JS "affine open cover of a fibre product"]
noncomputable def affineOpenCover
    (f : X ⟶ S) (g : Y ⟶ S) (𝒰 : S.AffineOpenCover)
    (𝒱 : ∀ i : 𝒰.I₀, ((𝒰.openCover.pullback₁ f).X i).AffineOpenCover)
    (𝒲 : ∀ i : 𝒰.I₀, ((𝒰.openCover.pullback₁ g).X i).AffineOpenCover) :
    (pullback f g).AffineOpenCover :=
  Scheme.AffineOpenCover.ofIsOpenCover
    (fun I : (openCover f g 𝒰 𝒱 𝒲).I₀ ↦
      ((openCover f g 𝒰 𝒱 𝒲).f I).opensRange)
    (openCover f g 𝒰 𝒱 𝒲).isOpenCover_opensRange
    (fun I ↦ isAffineOpen_opensRange ((openCover f g 𝒰 𝒱 𝒲).f I))

/-- The affine cover and the explicit chart cover determine the same open subset at every
index. -/
@[simp, stacks 01JS "affine chart range agrees with the explicit fibre-product cover"]
theorem affineOpenCover_opensRange
    (f : X ⟶ S) (g : Y ⟶ S) (𝒰 : S.AffineOpenCover)
    (𝒱 : ∀ i : 𝒰.I₀, ((𝒰.openCover.pullback₁ f).X i).AffineOpenCover)
    (𝒲 : ∀ i : 𝒰.I₀, ((𝒰.openCover.pullback₁ g).X i).AffineOpenCover)
    (I : (affineOpenCover f g 𝒰 𝒱 𝒲).I₀) :
    (((affineOpenCover f g 𝒰 𝒱 𝒲).openCover.f I).opensRange) =
      ((openCover f g 𝒰 𝒱 𝒲).f I).opensRange := sorry

end Scheme.Pullback
end AlgebraicGeometry
