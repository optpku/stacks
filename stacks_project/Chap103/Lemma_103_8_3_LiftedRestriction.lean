/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import stacks_project.Chap103.Lemma_103_8_3_LiftedSmallDirect
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous.Additive
public import stacks_project.Chap96.Lemma_96_10_1_Comparison
public import stacks_project.Chap66.Proposition_66_32_1_Comparison
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.GroupoidsOver FiberedCategoryOver.Groupoids
open scoped Bicategory
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.Modules
variable {S : Scheme.{u}}

/-- Modules on the existing canonical lifted small étale ringed site. -/
abbrev Lift (X : AlgebraicSpace S) := RingedSite.ModuleCat.{u + 1} (commRingedSiteLift X)

instance lift_abelian (X : AlgebraicSpace S) : Abelian (Lift X) := by
  -- Local instance justification (proof-local temporary data): bind the proved upper-universe additive sheafification.
  letI := SiteUniverse.additiveGroups X.smallEtaleTopology
  -- Local instance justification (proof-local temporary data): bind exactness for that same sheafification.
  letI := SiteUniverse.localBijections X.smallEtaleTopology
  infer_instance

instance lift_resolutions (X : AlgebraicSpace S) : HasInjectiveResolutions (Lift X) :=
  SheafOfModules.LargeSite.injectiveResolutions X.smallEtaleTopology (commRingedSiteLift X).structureSheaf

instance pushforwardLift_additive {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (pushforwardLift f).Additive := RingedSite.ToposHom.modulePushforward_additive (ringedToposHomLift f)

/-- Ordinary higher direct image of the canonical larger-universe pushforward. -/
def higherDirectImageLift {X Y : AlgebraicSpace S} (f : X ⟶ Y) (i : ℕ) : Lift X ⥤ Lift Y :=
  (pushforwardLift f).rightDerived i

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.GroupoidsOver
variable {S : Scheme.{u}}

/-- The actual inverse-image coefficient map, transported by identity coefficient bridges. -/
def moduleInverseCoefficientLift {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    (commEtaleRingedSiteLift X).structureSheaf ⟶
      ((toFunctor f).sheafPushforwardContinuous RingCat.{u + 1} X.etaleTopology Y.etaleTopology).obj
        (commEtaleRingedSiteLift Y).structureSheaf :=
  ObjectProperty.homMk
    ((ModuleUniverseComparison.coefficientIso X).inv.hom ≫
      Functor.whiskerRight (etaleStructureSheafMap f).hom SheafOfModules.UniverseLift.ringFunctor ≫
      (toFunctor f).op.whiskerLeft (ModuleUniverseComparison.coefficientIso Y).hom.hom)

/-- Restriction/inverse image along the actual total functor, on canonical lifted coefficients. -/
def moduleInverseImageLift {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    EtaleModulesLift Y ⥤ EtaleModulesLift X :=
  SheafOfModules.pushforward.{u + 1} (moduleInverseCoefficientLift f)

/-- The original pi coefficient map, transported to existing lifted ringed sites. -/
def representingCoefficientLift {U : AlgebraicSpace S} {X : GroupoidsOver S} (e : U.toGroupoids ≌ X) :
    (AlgebraicSpace.commRingedSiteLift U).structureSheaf ⟶
      ((smallEtaleFunctor U X e).sheafPushforwardContinuous RingCat.{u + 1} U.smallEtaleTopology X.etaleTopology).obj
        (commEtaleRingedSiteLift X).structureSheaf :=
  ObjectProperty.homMk
    ((AlgebraicSpace.ModuleUniverseComparison.coefficientIso U).inv.hom ≫
      Functor.whiskerRight (pi U X e).structureSheafMap.hom SheafOfModules.UniverseLift.ringFunctor ≫
      (smallEtaleFunctor U X e).op.whiskerLeft (ModuleUniverseComparison.coefficientIso X).hom.hom)

/-- Restriction to a represented small étale site uses its actual pi map. -/
def moduleRepresentingRestrictionLift {U : AlgebraicSpace S} {X : GroupoidsOver S} (e : U.toGroupoids ≌ X) :
    EtaleModulesLift X ⥤ AlgebraicSpace.Modules.Lift U :=
  SheafOfModules.pushforward.{u + 1} (representingCoefficientLift e)

/-- The original Yoneda representative of the supplied target object. -/
abbrev moduleSliceHom {Y : GroupoidsOver S} (y : Y.total) : GroupoidsOver.slice (Y.p.obj y) ⟶ Y :=
  YonedaSlice.representative (⟨y,rfl⟩ : Y.p.Fiber (Y.p.obj y))

/-- Small-site restriction at the actual object y, in the canonical larger presentation. -/
def moduleAtObjectLift {Y : GroupoidsOver S} (y : Y.total) :
    EtaleModulesLift Y ⥤ AlgebraicSpace.Modules.Lift (AlgebraicSpace.ofOver (Y.p.obj y)) :=
  moduleInverseImageLift (moduleSliceHom y) ⋙
    moduleRepresentingRestrictionLift (AlgebraicSpace.ofOverSliceEquiv (Y.p.obj y))

instance moduleInverseImageLift_additive {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    (moduleInverseImageLift f).Additive := by unfold moduleInverseImageLift; infer_instance

instance moduleRepresentingRestrictionLift_additive {U : AlgebraicSpace S} {X : GroupoidsOver S}
    (e : U.toGroupoids ≌ X) : (moduleRepresentingRestrictionLift e).Additive := by
  unfold moduleRepresentingRestrictionLift
  infer_instance

instance moduleAtObjectLift_additive {Y : GroupoidsOver S} (y : Y.total) :
    (moduleAtObjectLift y).Additive := by unfold moduleAtObjectLift; infer_instance

/-- The explicit lift of scheme coefficients identifies with its existing lifted ringed site. -/
def schemeCoefficientLiftIso (V : Over S) :
    SheafOfModules.UniverseLift.ring (Scheme.Etale.Small.structureSheaf V.left) ≅
      (Scheme.Etale.Small.liftedRingedSite V.left).structureSheaf :=
  (fullyFaithfulSheafToPresheaf V.left.smallEtaleTopology RingCat.{u + 1}).preimageIso
    (NatIso.ofComponents (fun _ => Iso.refl _) (by intros; ext x; rfl))

instance schemeEtaleComparisonLift_continuous (V : Over S) :
    (AlgebraicSpace.schemeEtaleRingedHom V).base.IsContinuous V.left.smallEtaleTopology
      (AlgebraicSpace.ofOver V).smallEtaleTopology :=
  (AlgebraicSpace.schemeEtaleToSmallEtale_isMorphismOfSites V).toIsContinuous

/-- Return to the existing canonical scheme small étale ringed site. -/
def modulesToSchemeLift (V : Over S) :
    AlgebraicSpace.Modules.Lift (AlgebraicSpace.ofOver V) ⥤
      RingedSite.ModuleCat.{u + 1} (Scheme.Etale.Small.liftedRingedSite V.left) :=
  SheafOfModules.pushforward.{u + 1} (ObjectProperty.homMk
    ((schemeCoefficientLiftIso V).inv.hom ≫
      Functor.whiskerRight (AlgebraicSpace.schemeEtaleRingedHom V).structureSheafMap.hom
        SheafOfModules.UniverseLift.ringFunctor ≫
      (AlgebraicSpace.schemeEtaleRingedHom V).base.op.whiskerLeft
        (AlgebraicSpace.ModuleUniverseComparison.coefficientIso (AlgebraicSpace.ofOver V)).hom.hom))

end AlgebraicGeometry.GroupoidsOver
