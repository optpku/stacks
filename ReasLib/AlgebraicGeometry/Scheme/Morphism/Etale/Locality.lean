/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X S : Scheme.{u}}

/-- Étaleness of a scheme morphism is equivalent to being locally of type
`RingHom.Etale`. -/
theorem etale_iff_locallyOfType (f : X ⟶ S) :
    Etale f ↔ LocallyOfType RingHom.Etale f := by
  rw [locallyOfType_iff_affineLocally RingHom.Etale f RingHom.Etale.propertyIsLocal]
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
      ∃ 𝒱 : S.AffineOpenCover, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover,
          ∀ i : 𝒰.I₀,
            RingHom.Etale (((𝒰.f i ≫ 𝒱.openCover.pullbackHom f j).appTop).hom) := by
  simpa [etale_iff_locallyOfType] using
    (locallyOfType_iff_exists_affineOpenCover
      RingHom.Etale RingHom.Etale.propertyIsLocal)

end Scheme.Hom
end AlgebraicGeometry
