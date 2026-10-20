/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyOfType

/-!
# Locality of smooth scheme morphisms

This file relates smoothness to the generic local ring-map-property interface and gives open-cover
and affine-open-cover criteria for smooth scheme morphisms.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X S : Scheme.{u}}

/-- Smoothness of a scheme morphism is equivalent to being locally of type
`RingHom.Smooth`. -/
theorem smooth_iff_locallyOfType (f : X ⟶ S) :
    Smooth f ↔ LocallyOfType RingHom.Smooth f := by
  rw [locallyOfType_iff_affineLocally RingHom.Smooth f RingHom.Smooth.propertyIsLocal]
  rw [smooth_iff, affineLocally_iff_forall_isAffineOpen]

/-- A scheme morphism is smooth if and only if the target has an open cover whose pullbacks
have open covers by smooth morphisms. -/
theorem smooth_iff_exists_openCover (f : X ⟶ S) :
    Smooth f ↔
      ∃ 𝒱 : S.OpenCover, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.pullback₁ f).X j).OpenCover,
          ∀ i : 𝒰.I₀, Smooth (𝒰.f i ≫ 𝒱.pullbackHom f j) := by
  simpa [smooth_iff_locallyOfType] using
    (locallyOfType_iff_exists_openCover RingHom.Smooth RingHom.Smooth.propertyIsLocal)

/-- A scheme morphism is smooth if and only if the target has an affine open cover whose
pullbacks have affine open covers with smooth induced maps on global sections. -/
theorem smooth_iff_exists_affineOpenCover (f : X ⟶ S) :
    Smooth f ↔
      ∃ 𝒱 : S.AffineOpenCover, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover,
          ∀ i : 𝒰.I₀,
            RingHom.Smooth (((𝒰.f i ≫ 𝒱.openCover.pullbackHom f j).appTop).hom) := by
  simpa [smooth_iff_locallyOfType] using
    (locallyOfType_iff_exists_affineOpenCover
      RingHom.Smooth RingHom.Smooth.propertyIsLocal)

end Scheme.Hom
end AlgebraicGeometry
