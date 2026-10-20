/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.UniverseLift
public import stacks_project.Chap84.Lemma_84_7_2_Comparison
public import stacks_project.Chap85.Lemma_85_34_2_Pullback

/-!
# Derived unit along the spaces-étale augmentation

The Section 85.32 morphism of ringed topoi `spacesEtaleAugmentationRinged` is
presented as a morphism of ringed sites. After the carrier lift to
`ModuleCat.{u + 1}`, a module `F` on `X_spaces,étale` has a canonical map
`F ⟶ Ra_*(a^* F)` in the unbounded derived category, obtained by transporting
the underived adjunction unit through `ordinaryToRightDerived`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.AssociatedModule
open Functor
open RingedSite.Hom
open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- The presenting functor of the spaces-étale augmentation is a morphism of
sites. -/
instance augmentationFunctor_isMorphismOfSites :
    IsMorphismOfSites (spacesEtaleTopology X) (spacesEtaleTotalTopology U)
      (augmentationFunctor U a) :=
  sorry

/-- The spaces-étale augmentation as a morphism of ringed sites, with base
`augmentationFunctor` and the Section 85.32 structure-sheaf map. -/
def spacesEtaleAugmentationHom :
    RingedSite.Hom (etaleTotalRingedSite U) (spacesRingedSite X) where
  base := augmentationFunctor U a
  structureSheafMap := spacesEtaleAugmentationRinged_structureSheafMap U a

/-- The base functor of `spacesEtaleAugmentationHom` is `augmentationFunctor`. -/
theorem spacesEtaleAugmentationHom_base :
    (spacesEtaleAugmentationHom a).base = augmentationFunctor U a :=
  sorry

/-- The structure-sheaf map of `spacesEtaleAugmentationHom` is the Section 85.32
direct-image comparison. -/
theorem spacesEtaleAugmentationHom_structureSheafMap :
    (spacesEtaleAugmentationHom a).structureSheafMap =
      spacesEtaleAugmentationRinged_structureSheafMap U a :=
  sorry

/-- Module pushforward along the spaces-étale augmentation, at carrier universe
`u + 1`, is a right adjoint. -/
instance modulePushforward_isRightAdjoint :
    (spacesEtaleAugmentationHom a).modulePushforward.{u + 1}.IsRightAdjoint :=
  sorry

/-- The total right-derived functor of module pushforward along the spaces-étale
augmentation exists at carrier universe `u + 1`. -/
instance hasRightDerived_modulePushforwardDerived :
    Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u + 1} (spacesEtaleAugmentationHom a))
      (ModuleQis.{u + 1} (etaleTotalRingedSite U)) :=
  sorry

/-- The underived adjunction unit `F ⟶ a_*(a^* F)` after the carrier lift. -/
def ordinaryUnit (F : RingedSite.ModuleCat.{u} (spacesRingedSite X)) :
    RingedSite.Module.carrierLift (spacesRingedSite X) F ⟶
      (spacesEtaleAugmentationHom a).modulePushforward.{u + 1}.obj
        ((spacesEtaleAugmentationHom a).modulePullback.{u + 1}.obj
          (RingedSite.Module.carrierLift (spacesRingedSite X) F)) :=
  (modulePullbackPushforwardAdjunction.{u + 1} (spacesEtaleAugmentationHom a)).unit.app
    (RingedSite.Module.carrierLift (spacesRingedSite X) F)

/-- `ordinaryUnit` is the Hom-level module adjunction unit at the carrier lift of
`F`. -/
theorem ordinaryUnit_eq (F : RingedSite.ModuleCat.{u} (spacesRingedSite X)) :
    ordinaryUnit a F =
      (modulePullbackPushforwardAdjunction.{u + 1} (spacesEtaleAugmentationHom a)).unit.app
        (RingedSite.Module.carrierLift (spacesRingedSite X) F) :=
  sorry

/-- The canonical map `F ⟶ Ra_*(a^* F)` in the derived category, after the
carrier lift. -/
def toPushforwardDerived (F : RingedSite.ModuleCat.{u} (spacesRingedSite X)) :=
  ordinaryToRightDerived (spacesEtaleAugmentationHom a)
    ((spacesEtaleAugmentationHom a).modulePullback.{u + 1}.obj
      (RingedSite.Module.carrierLift (spacesRingedSite X) F))
    (RingedSite.Module.carrierLift (spacesRingedSite X) F) (ordinaryUnit a F)

/-- `toPushforwardDerived` is `ordinaryToRightDerived` of `ordinaryUnit`. -/
theorem toPushforwardDerived_eq (F : RingedSite.ModuleCat.{u} (spacesRingedSite X)) :
    toPushforwardDerived a F =
      ordinaryToRightDerived (spacesEtaleAugmentationHom a)
        ((spacesEtaleAugmentationHom a).modulePullback.{u + 1}.obj
          (RingedSite.Module.carrierLift (spacesRingedSite X) F))
        (RingedSite.Module.carrierLift (spacesRingedSite X) F) (ordinaryUnit a F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
