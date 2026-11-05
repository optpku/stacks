/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyOfType

/-!
# Locality of étale scheme morphisms

This file relates étaleness to the generic local ring-map-property interface and gives open-cover
and affine-open-cover criteria for étale scheme morphisms.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/-- Etale ring maps remain so after precomposition with a source localization. -/
theorem RingHom.Etale.stableUnderCompositionWithLocalizationAwaySource :
    RingHom.StableUnderCompositionWithLocalizationAwaySource RingHom.Etale := by
  apply (RingHom.Etale.stableUnderComposition.stableUnderCompositionWithLocalizationAway
    ?_).left
  intro R T _ _ _ r _
  exact RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway r)

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X S : Scheme.{u}}

/-- Étaleness of a scheme morphism is equivalent to being locally of type
`RingHom.Etale`. -/
theorem etale_iff_locallyOfType (f : X ⟶ S) :
    Etale f ↔ LocallyOfType RingHom.Etale f := by
  rw [locallyOfType_iff_affineLocally RingHom.Etale f RingHom.Etale.propertyIsLocal
    RingHom.Etale.stableUnderCompositionWithLocalizationAwaySource]
  rw [etale_iff, affineLocally_iff_forall_isAffineOpen]

/-- An étale scheme morphism is locally induced by étale ring homomorphisms. -/
instance instLocallyOfTypeRingHomEtaleOfEtale (f : X ⟶ S) [Etale f] :
    LocallyOfType RingHom.Etale f :=
  (etale_iff_locallyOfType f).mp inferInstance

/-- A scheme morphism is étale if and only if the target has an open cover whose pullbacks
have open covers by étale morphisms. -/
theorem etale_iff_exists_openCover (f : X ⟶ S) :
    Etale f ↔
      ∃ 𝒱 : S.OpenCover, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.pullback₁ f).X j).OpenCover,
          ∀ i : 𝒰.I₀, Etale (𝒰.f i ≫ 𝒱.pullbackHom f j) := by
  simpa [etale_iff_locallyOfType] using
    (locallyOfType_iff_exists_openCover RingHom.Etale RingHom.Etale.propertyIsLocal)

/-- A scheme morphism is étale if and only if the target has an affine open cover whose
pullbacks have affine open covers with étale induced maps on global sections. -/
theorem etale_iff_exists_affineOpenCover (f : X ⟶ S) :
    Etale f ↔
      ∃ 𝒱 : S.AffineOpenCover.{u}, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover.{u},
          ∀ i : 𝒰.I₀,
            RingHom.Etale (((𝒰.f i ≫ 𝒱.openCover.pullbackHom f j).appTop).hom) := by
  simpa [etale_iff_locallyOfType] using
    (locallyOfType_iff_exists_affineOpenCover
      RingHom.Etale RingHom.Etale.propertyIsLocal
      RingHom.Etale.stableUnderCompositionWithLocalizationAwaySource)

end Scheme.Hom
end AlgebraicGeometry
