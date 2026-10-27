/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Existence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.QCoh.Derived
public import stacks_project.Chap85.Lemma_85_34_3_Derived

/-! # Enlarged-universe derived augmentation compatibility -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open Functor RingedSite.Hom
open scoped Simplicial

noncomputable section

set_option backward.privateInPublic true
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- Coefficient lifting retains the presenting augmentation's actual site and structure maps. -/
private def liftedCompatibilityHom :
    RingedSite.Hom
      (RingedSite.ofRingSheaf (etaleTotalRingedSite U).siteTopology
        (SheafOfModules.CoefficientLift.ring (etaleTotalRingedSite U).structureSheaf))
      (RingedSite.ofRingSheaf (spacesRingedSite X).siteTopology
        (SheafOfModules.CoefficientLift.ring (spacesRingedSite X).structureSheaf)) where
  base := (spacesEtaleAugmentationHom a).base
  isMorphismOfSites := (spacesEtaleAugmentationHom a).isMorphismOfSites
  structureSheafMap := ⟨Functor.whiskerRight (spacesEtaleAugmentationHom a).structureSheafMap.hom
    SheafOfModules.UniverseLift.ringFunctor⟩

/-- With equal coefficient and carrier universes the actual sheafification adjoint exists. -/
private theorem liftedCompatibilityRightAdjoint :
    ((liftedCompatibilityHom a).modulePushforward.{u + 1}).IsRightAdjoint := by
  dsimp [RingedSite.Hom.modulePushforward]
  infer_instance

/-- The conjugated coefficient-lifted direct image has the original section functions. -/
private def compatibilityPushforwardIso :
    (SheafOfModules.CoefficientLift.equivalence (etaleTotalRingedSite U).structureSheaf).functor ⋙
        (liftedCompatibilityHom a).modulePushforward.{u + 1} ⋙
        (SheafOfModules.CoefficientLift.equivalence (spacesRingedSite X).structureSheaf).inverse ≅
      (spacesEtaleAugmentationHom a).modulePushforward.{u + 1} :=
  NatIso.ofComponents (fun M ↦
    let P := ((SheafOfModules.CoefficientLift.equivalence
      (etaleTotalRingedSite U).structureSheaf).functor ⋙
        (liftedCompatibilityHom a).modulePushforward.{u + 1} ⋙
        (SheafOfModules.CoefficientLift.equivalence (spacesRingedSite X).structureSheaf).inverse).obj M
    let Q := (spacesEtaleAugmentationHom a).modulePushforward.{u + 1}.obj M
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun V ↦
        { hom := ModuleCat.ofHom (X := P.val.obj V) (Y := Q.val.obj V)
            { toFun := fun m ↦ m
              map_add' := fun _ _ ↦ rfl
              map_smul' := fun _ _ ↦ rfl }
          inv := ModuleCat.ofHom (X := Q.val.obj V) (Y := P.val.obj V)
            { toFun := fun m ↦ m
              map_add' := fun _ _ ↦ rfl
              map_smul' := fun _ _ ↦ rfl }
          hom_inv_id := by ext m; rfl
          inv_hom_id := by ext m; rfl }) (fun {_ _} g ↦ by ext m; rfl)))
    (fun g ↦ by ext V m; rfl)

/-- The presenting augmentation's right-adjoint certificate contains the concrete lifted adjoint. -/
private theorem compatibilityRightAdjoint :
    ((spacesEtaleAugmentationHom a).modulePushforward.{u + 1}).IsRightAdjoint :=
  by
    -- Local instance justification (proof-local temporary data): the coefficient-conjugated functor uses the completed adjoint of this particular lifted augmentation.
    letI := liftedCompatibilityRightAdjoint a
    exact Functor.isRightAdjoint_of_iso (compatibilityPushforwardIso a)

/-- Total-site section rings are the commutative geometric global-section rings. -/
private theorem compatibilityTotalComm (V : (SpacesEtale U)ᵒᵖ)
    (x y : (etaleTotalRingedSite U).structureSheaf.obj.obj V) : x * y = y * x :=
  @mul_comm (globalSectionsRing V.unop.obj.left) _ x y

/-- Spaces-étale section rings inherit commutativity from their geometric global sections. -/
private theorem compatibilityBaseComm (V : (spacesEtaleSite X)ᵒᵖ)
    (x y : (spacesRingedSite X).structureSheaf.obj.obj V) : x * y = y * x := by
  let e := Iso.ringCatIsoToRingEquiv
    (asIso (Etale.Big.spacesStructureToGamma V.unop) ≪≫
      Etale.Big.gammaGlobalSectionsIso V.unop.left)
  apply e.injective
  simp only [map_mul]
  exact @mul_comm (globalSectionsRing V.unop.left) _ (e x) (e y)

/-- The enlarged-universe direct-image certificate stores the actual K-injective extension. -/
private theorem compatibilityHasPushforward :
    Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u + 1} (spacesEtaleAugmentationHom a))
      (ModuleQis.{u + 1} (etaleTotalRingedSite U)) :=
  Functor.KInjectiveModel.Homotopy.hasRightDerived
    ((spacesEtaleAugmentationHom a).modulePushforward.{u + 1})

/-- The total left-derived functor of the presenting module inverse image exists at the
original enlarged carrier universe. -/
instance hasLeftDerived_modulePullbackToDerived :
    Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{u + 1} (spacesEtaleAugmentationHom a))
      (ModuleQis.{u + 1} (spacesRingedSite X)) := by
  -- Local instance justification (proof-local temporary data): the complete lifted adjunction supplies the actual inverse-image model before its universal certificate.
  letI := compatibilityRightAdjoint a
  exact DerivedExistence.hasPullback (spacesEtaleAugmentationHom a)
    (compatibilityTotalComm (U := U)) (compatibilityBaseComm (X := X))

/-- The enlarged-universe total-derived pair uses actual cell and K-injective extension maps. -/
instance derivedAdjunction_hasPair :
    DerivedAdjunction.HasPair.{u + 1} (spacesEtaleAugmentationHom a) := by
  -- Local instance justification (proof-local temporary data): retain the concrete lifted module adjunction in the original compatibility presentation.
  letI := compatibilityRightAdjoint a
  -- Local instance justification (proof-local temporary data): retain the complete K-injective existence certificate instead of selecting data from unfinished existence.
  letI := compatibilityHasPushforward a
  exact DerivedExistence.hasPair (spacesEtaleAugmentationHom a)
    (compatibilityTotalComm (U := U)) (compatibilityBaseComm (X := X))

/-- The enlarged-universe derived module adjunction of the presenting spaces-étale augmentation. -/
abbrev derivedModuleAdjunction :
    modulePullbackDerived.{u + 1} (spacesEtaleAugmentationHom a) ⊣
      modulePushforwardDerived.{u + 1} (spacesEtaleAugmentationHom a) := by
  -- Local instance justification (defeq pin): proof irrelevance preserves the established public type while the complete lifted certificate selects the actual module adjunction.
  letI := compatibilityRightAdjoint a
  -- Local instance justification (proof-local temporary data): the canonical derived direct image is selected from its completed actual K-injective witness.
  letI := compatibilityHasPushforward a
  exact moduleDerivedAdjunction.{u + 1} (spacesEtaleAugmentationHom a)

end AlgebraicGeometry.AlgebraicSpace.Simplicial
