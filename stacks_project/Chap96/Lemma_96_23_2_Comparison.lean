/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward
public import ReasLib.CategoryTheory.Sites.MorphismOfSites.Topology
public import ReasLib.CategoryTheory.Sites.TopologyComparison.Absolute
public import stacks_project.Chap96.Definition_96_11_1_QCoh
public import stacks_project.Chap96.Lemma_96_12_4_LQCoh

/-!
# Identity comparison of fppf and étale ringed sites

The identity functor of a category fibred in groupoids is a morphism of ringed
sites `ε : X_fppf → X_étale`. Direct image along `ε` is restriction of fppf
modules to the étale topology; an étale module that is already an fppf sheaf
packages as an fppf module on the same underlying presheaf.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The associated étale topology of `X` is coarser than the associated fppf
topology. -/
theorem etale_le_fppf (X : GroupoidsOver S) :
    X.etaleTopology ≤ X.fppfTopology := sorry

/-- The étale ringed site of `X` is coarser than the fppf ringed site. -/
theorem etaleRingedSite_le_fppfRingedSite (X : GroupoidsOver S) :
    (etaleRingedSite X).siteTopology ≤ (fppfRingedSite X).siteTopology := sorry

/-- The identity functor is continuous from the étale topology to the fppf
topology of `X`. -/
instance instEtaleIdIsContinuousFppf (X : GroupoidsOver S) :
    (𝟭 X.total).IsContinuous X.etaleTopology X.fppfTopology :=
  Functor.id_isContinuous_of_le (etale_le_fppf X)

/-- The identity functor is continuous from the étale ringed site of `X` to the
fppf ringed site. -/
instance instEtaleIdIsContinuousFppfRinged (X : GroupoidsOver S) :
    (𝟭 X.total).IsContinuous
      (etaleRingedSite X).siteTopology (fppfRingedSite X).siteTopology :=
  Functor.id_isContinuous_of_le (etaleRingedSite_le_fppfRingedSite X)

/-- The identity functor is a morphism of sites `X_fppf → X_étale`. -/
instance instEtaleIdIsMorphismOfSites (X : GroupoidsOver S) :
    IsMorphismOfSites X.etaleTopology X.fppfTopology (𝟭 X.total) :=
  IsMorphismOfSites.id_of_le (etale_le_fppf X)

/-- The identity functor is a morphism of sites from the fppf ringed site of `X`
to the étale ringed site. -/
instance instEtaleIdIsMorphismOfSitesRinged (X : GroupoidsOver S) :
    IsMorphismOfSites
      (etaleRingedSite X).siteTopology (fppfRingedSite X).siteTopology
      (𝟭 X.total) :=
  IsMorphismOfSites.id_of_le (etaleRingedSite_le_fppfRingedSite X)

/-- Identity-on-sections comparison from the étale structure sheaf to the
direct image of the fppf structure sheaf. -/
def etaleToFppfStructureSheafMap (X : GroupoidsOver S) :
    (etaleRingedSite X).structureSheaf ⟶
      ((𝟭 X.total).sheafPushforwardContinuous RingCat.{u}
        (etaleRingedSite X).siteTopology
        (fppfRingedSite X).siteTopology).obj
        (fppfRingedSite X).structureSheaf :=
  Sheaf.homEquiv.symm
    { app := fun _ ↦ 𝟙 _
      naturality := fun _ _ _ ↦ sorry }

/-- The identity-on-objects morphism of ringed sites `ε : X_fppf → X_étale`. -/
def etaleFppfHom (X : GroupoidsOver S) :
    RingedSite.Hom (fppfRingedSite X) (etaleRingedSite X) where
  base := 𝟭 X.total
  isMorphismOfSites := instEtaleIdIsMorphismOfSitesRinged X
  structureSheafMap := etaleToFppfStructureSheafMap X

/-- The base of `etaleFppfHom X` is the identity functor of `X`. -/
theorem etaleFppfHom_base (X : GroupoidsOver S) :
    (etaleFppfHom X).base = 𝟭 X.total := sorry

/-- The structure-sheaf map of `etaleFppfHom X` is the identity-on-Γ
comparison `etaleToFppfStructureSheafMap`. -/
theorem etaleFppfHom_structureSheafMap (X : GroupoidsOver S) :
    (etaleFppfHom X).structureSheafMap = etaleToFppfStructureSheafMap X := sorry

/-- Components of `etaleToFppfStructureSheafMap` are identities of global
sections. -/
theorem etaleToFppfStructureSheafMap_app (X : GroupoidsOver S) (x : X.total) :
    (etaleToFppfStructureSheafMap X).hom.app (op x) = 𝟙 _ := sorry

/-- The category of fppf `𝒪_X`-modules is abelian. -/
instance fppfModulesAbelian (X : GroupoidsOver S) :
    Abelian (RingedSite.ModuleCat.{u} (fppfRingedSite X)) where
  toPreadditive := inferInstance
  toIsNormalMonoCategory := sorry
  toIsNormalEpiCategory := sorry
  has_finite_products := sorry
  has_kernels := sorry
  has_cokernels := sorry

/-- Package an étale `𝒪_X`-module that is already an fppf sheaf as an fppf
`𝒪_X`-module, on the same underlying module presheaf. -/
def toFppfModule {X : GroupoidsOver S} (F : etaleModules X)
    (hF : Presheaf.IsSheaf (fppfRingedSite X).siteTopology
      (etaleModulePresheaf F).presheaf) :
    RingedSite.ModuleCat.{u} (fppfRingedSite X) where
  val := etaleModulePresheaf F
  isSheaf := hF

/-- `toFppfModule F hF` has underlying module presheaf `etaleModulePresheaf F`. -/
theorem toFppfModule_val {X : GroupoidsOver S} (F : etaleModules X)
    (hF : Presheaf.IsSheaf (fppfRingedSite X).siteTopology
      (etaleModulePresheaf F).presheaf) :
    (toFppfModule F hF).val = etaleModulePresheaf F := sorry

/-- Direct image of abelian sheaves along `ε : X_fppf → X_étale`. -/
abbrev abelianPushforward_etaleFppf (X : GroupoidsOver S) :
    Sheaf X.fppfTopology AddCommGrpCat.{u} ⥤
      Sheaf X.etaleTopology AddCommGrpCat.{u} :=
  GrothendieckTopology.TopologyComparison.pushforward AddCommGrpCat.{u}
    (etale_le_fppf X)

/-- `abelianPushforward_etaleFppf` is topology-comparison pushforward along
`etale_le_fppf`. -/
theorem abelianPushforward_etaleFppf_eq (X : GroupoidsOver S) :
    abelianPushforward_etaleFppf X =
      GrothendieckTopology.TopologyComparison.pushforward AddCommGrpCat.{u}
        (etale_le_fppf X) := sorry

/-- Underlying abelian sheaf of an étale `𝒪_X`-module. -/
abbrev etaleAbelianSheaf {X : GroupoidsOver S} (F : etaleModules X) :
    Sheaf X.etaleTopology AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (etaleRingedSite X).structureSheaf).obj F

/-- Underlying abelian sheaf of the fppf packaging of an étale module. -/
abbrev fppfAbelianSheaf {X : GroupoidsOver S} (F : etaleModules X)
    (hF : Presheaf.IsSheaf (fppfRingedSite X).siteTopology
      (etaleModulePresheaf F).presheaf) :
    Sheaf (fppfRingedSite X).siteTopology AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (fppfRingedSite X).structureSheaf).obj (toFppfModule F hF)

/-- Direct image of fppf modules along `etaleFppfHom` is additive. -/
instance etaleFppfHom_modulePushforward_additive (X : GroupoidsOver S) :
    (etaleFppfHom X).modulePushforward.{u}.Additive := inferInstance

/-- Direct image of fppf modules along `etaleFppfHom` is a right adjoint, so
inverse image along `ε` exists. -/
instance etaleFppfHom_modulePushforward_isRightAdjoint (X : GroupoidsOver S) :
    (etaleFppfHom X).modulePushforward.{u}.IsRightAdjoint := sorry

/-- Fppf modules on `X` admit injective resolutions. -/
instance fppfModules_hasInjectiveResolutions (X : GroupoidsOver S) :
    HasInjectiveResolutions (RingedSite.ModuleCat.{u} (fppfRingedSite X)) :=
  sorry

/-- Abelian groups have weak sheafification on the fppf ringed site of `X`. -/
instance fppfRingedSite_hasWeakSheafify_addCommGrpCat (X : GroupoidsOver S) :
    HasWeakSheafify (fppfRingedSite X).siteTopology AddCommGrpCat.{u} := sorry

/-- Pointwise left Kan extensions along the identity exist for abelian
presheaves on `X`. -/
instance id_op_hasLeftKanExtension_addCommGrpCat (X : GroupoidsOver S)
    (P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (𝟭 X.total).op.HasLeftKanExtension P := sorry

/-- fppf-sheafification of an étale abelian sheaf along the identity
comparison `ε`. -/
noncomputable abbrev sheafifyEtaleToFppf (X : GroupoidsOver S)
    (G : Sheaf (etaleRingedSite X).siteTopology AddCommGrpCat.{u}) :
    Sheaf (fppfRingedSite X).siteTopology AddCommGrpCat.{u} :=
  (GrothendieckTopology.TopologyComparison.pullback AddCommGrpCat.{u}
    (etaleRingedSite_le_fppfRingedSite X)).obj G

/-- `sheafifyEtaleToFppf` is topology-comparison pullback along
`etaleRingedSite_le_fppfRingedSite`. -/
theorem sheafifyEtaleToFppf_eq (X : GroupoidsOver S)
    (G : Sheaf (etaleRingedSite X).siteTopology AddCommGrpCat.{u}) :
    sheafifyEtaleToFppf X G =
      (GrothendieckTopology.TopologyComparison.pullback AddCommGrpCat.{u}
        (etaleRingedSite_le_fppfRingedSite X)).obj G := sorry

end AlgebraicGeometry.GroupoidsOver
