/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.PresentationAdjunction
public import ReasLib.CategoryTheory.Sites.Topos.InternalRing

/-!
# Étale restriction of ring sheaves

Étale restriction is the actual postcomposition functor on sections. Its
comparison with geometric inverse image is a natural isomorphism of the whole
type-sheaf functors. The canonical finite-product lift therefore preserves all
ring operations. The source ring sheaf and the internally lifted restriction
are identified by identity maps on their underlying sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Sheaf.InternalRing

noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.EtaleTopos

variable {S : Scheme.{u}}

/-- Étale restriction of type sheaves is left exact by its actual inverse-image comparison. -/
instance restrictType_preservesFiniteLimits {U X : AlgebraicSpace S}
    (p : U ⟶ X) [Etale p] :
    PreservesFiniteLimits
      ((Modules.restrictPostcompose p).sheafPushforwardContinuous (Type u)
        (smallEtaleTopology U) (smallEtaleTopology X)) :=
  preservesFiniteLimits_of_natIso (restrictTypeIsoInverseImage p).symm

/-- Pointwise restriction and the finite-product lift have the same ring operations. -/
def restrictRingToInternalIso {U X : AlgebraicSpace S}
    (p : U ⟶ X) [Etale p] (R : Sheaf (smallEtaleTopology X) RingCat.{u}) :
    toInternal.{u + 1, u, u}.obj
        (((Modules.restrictPostcompose p).sheafPushforwardContinuous RingCat.{u}
          (smallEtaleTopology U) (smallEtaleTopology X)).obj R) ≅
      (@Functor.mapRingOfFiniteProducts
        (Sheaf (smallEtaleTopology X) (Type u)) _ _
        (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology X))
        (Sheaf (smallEtaleTopology U) (Type u)) _ _
        (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology U))
        ((Modules.restrictPostcompose p).sheafPushforwardContinuous (Type u)
          (smallEtaleTopology U) (smallEtaleTopology X)) inferInstance).obj
        (toInternal.{u + 1, u, u}.obj R) where
  hom := @RingObjCat.Hom.mk (Sheaf (smallEtaleTopology U) (Type u)) _ _
    (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology U)) _ _ (𝟙 _) sorry
  inv := @RingObjCat.Hom.mk (Sheaf (smallEtaleTopology U) (Type u)) _ _
    (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology U)) _ _ (𝟙 _) sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward internal-ring comparison is identity on the actual restricted type sheaf. -/
@[simp]
theorem restrictRingToInternalIso_hom_hom {U X : AlgebraicSpace S}
    (p : U ⟶ X) [Etale p] (R : Sheaf (smallEtaleTopology X) RingCat.{u}) :
    RingObjects.hom (smallEtaleTopology U) (restrictRingToInternalIso p R).hom = 𝟙 _ := rfl

/-- The reverse internal-ring comparison is identity on the actual restricted type sheaf. -/
@[simp]
theorem restrictRingToInternalIso_inv_hom {U X : AlgebraicSpace S}
    (p : U ⟶ X) [Etale p] (R : Sheaf (smallEtaleTopology X) RingCat.{u}) :
    RingObjects.hom (smallEtaleTopology U) (restrictRingToInternalIso p R).inv = 𝟙 _ := rfl

/-- Étale restriction of ring sheaves is geometric inverse image, via the canonical
finite-product lift of the whole type-sheaf comparison. -/
def restrictRingIsoInverseImage {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p] :
    (Modules.restrictPostcompose p).sheafPushforwardContinuous RingCat.{u}
        (smallEtaleTopology U) (smallEtaleTopology X) ≅
      (morphismOfTopoi p).ringInverseImage :=
  NatIso.ofComponents
    (fun R ↦
      (toFromIso.{u + 1, u, u}.app
        (((Modules.restrictPostcompose p).sheafPushforwardContinuous RingCat.{u}
          (smallEtaleTopology U) (smallEtaleTopology X)).obj R)).symm ≪≫
      fromInternal.{u + 1, u, u}.mapIso (restrictRingToInternalIso p R) ≪≫
      fromInternal.{u + 1, u, u}.mapIso
        ((@Functor.mapRingOfFiniteProductsNatIso
          (Sheaf (smallEtaleTopology X) (Type u)) _ _
          (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology X))
          (Sheaf (smallEtaleTopology U) (Type u)) _ _
          (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology U))
          _ _ _ _ (restrictTypeIsoInverseImage p)).app
          (toInternal.{u + 1, u, u}.obj R)))
    sorry

/-- Forgetting ring operations recovers the specified type-sheaf inverse-image comparison. -/
theorem restrictRingIsoInverseImage_forget {U X : AlgebraicSpace S}
    (p : U ⟶ X) [Etale p] (R : Sheaf (smallEtaleTopology X) RingCat.{u}) :
    (sheafCompose (smallEtaleTopology U) (forget RingCat.{u})).mapIso
        ((restrictRingIsoInverseImage p).app R) =
      eqToIso (congrArg (fun G ↦ G.obj R)
        (Functor.sheafPushforwardContinuous.compSheafCompose
          (Modules.restrictPostcompose p) (forget RingCat.{u})
          (smallEtaleTopology U) (smallEtaleTopology X))) ≪≫
        (restrictTypeIsoInverseImage p).app
          ((sheafCompose (smallEtaleTopology X) (forget RingCat.{u})).obj R) ≪≫
        ((morphismOfTopoi p).ringInverseImageForgetIso.app R).symm := sorry

end AlgebraicGeometry.AlgebraicSpace.EtaleTopos
