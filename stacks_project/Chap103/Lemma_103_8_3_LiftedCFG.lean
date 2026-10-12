/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import ReasLib.AlgebraicGeometry.RingedSite.Module.UniverseComparison
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.GrothendieckLarge
public import stacks_project.Chap96.Lemma_96_12_3_Pullback
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.FilteredColimits

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GroupoidsOver FiberedCategoryOver.Groupoids
noncomputable section
universe u

namespace CategoryTheory.SiteUniverse

/-- A value universe containing this site's objects admits type sheafification. -/
theorem types {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C) :
    HasSheafify J (Type (u + 1)) := by infer_instance

/-- The same universe admits additive-group sheafification. -/
theorem additiveGroups {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C) :
    HasSheafify J AddCommGrpCat.{u + 1} := by infer_instance

/-- The exact abelian sheafification is described by local bijections. -/
theorem localBijections {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C) :
    J.WEqualsLocallyBijective AddCommGrpCat.{u + 1} := by infer_instance

/-- The genuine full comma limit fits in the specified value universe. -/
theorem rightKan {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) (P : Cᵒᵖ ⥤ Type (u + 1)) : F.op.HasPointwiseRightKanExtension P := by
  intro V
  -- Local instance justification (defeq pin): the full structured-arrow index has objects in u+1.
  letI : HasLimitsOfShape (StructuredArrow V F.op) (Type (u + 1)) := by infer_instance
  infer_instance

end CategoryTheory.SiteUniverse

namespace AlgebraicGeometry.GroupoidsOver
variable {S : Scheme.{u}}

/-- The existing canonical enlarged étale module owner. -/
abbrev EtaleModulesLift (X : GroupoidsOver S) :=
  RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X)

instance etaleModulesLift_abelian (X : GroupoidsOver S) : Abelian (EtaleModulesLift X) := by
  -- Local instance justification (proof-local temporary data): bind the proved upper-universe additive sheafification.
  letI := SiteUniverse.additiveGroups X.etaleTopology
  -- Local instance justification (proof-local temporary data): use local-bijection exactness for the same sheafification.
  letI := SiteUniverse.localBijections X.etaleTopology
  infer_instance

/-- Actual injective resolutions on the canonical u+1 coefficient owner. -/
instance etaleModulesLift_resolutions (X : GroupoidsOver S) : HasInjectiveResolutions (EtaleModulesLift X) :=
  SheafOfModules.LargeSite.injectiveResolutions X.etaleTopology
    (commEtaleRingedSiteLift X).structureSheaf

/-- The original specified inverse coefficient composite, without selecting
an inverse through etaleStructureSheafMap_isIso. -/
def etaleInverseCoefficientData {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    (toFunctor f).op ⋙ (etaleStructureSheaf Y).obj ⟶ (etaleStructureSheaf X).obj :=
  ((inverseImageEtaleStructureSheafIso f).inv ≫
    CategoryTheory.Sheaf.ringSheafOfCommMap.{u,u+1,u} (commEtaleStructureSheafIso f).hom).hom

/-- Transport the genuine coefficient map to the EXISTING commutative lifted sites. -/
def etaleInverseCoefficientLift {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    (toFunctor f).op ⋙ (commEtaleRingedSiteLift Y).structureSheaf.obj ⟶
      (commEtaleRingedSiteLift X).structureSheaf.obj :=
  (toFunctor f).op.whiskerLeft (ModuleUniverseComparison.coefficientIso Y).inv.hom ≫
    SheafOfModules.UniverseLift.ringMap (etaleStructureSheaf X) (toFunctor f)
      (etaleStructureSheaf Y) (etaleInverseCoefficientData f) ≫
    (ModuleUniverseComparison.coefficientIso X).hom.hom

/-- The canonical cocontinuous direct-image factory on the existing lifted
ringed sites, with actual upper-universe sheafification and comma limits. -/
def moduleDirectImageToposHomLift {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    RingedSite.ToposHom (commEtaleRingedSiteLift X) (commEtaleRingedSiteLift Y) := by
  -- Local instance justification (defeq pin): the cartesian total functor supplies this exact inherited-topology certificate.
  letI : (toFunctor f).IsCocontinuous X.etaleTopology Y.etaleTopology :=
    CartesianBasedFunctor.inheritedTopology.isCocontinuous (toCartesianBasedFunctor f)
      (StandardTopology.etale.overTopology S)
  -- Local instance justification (proof-local temporary data): this geometric factory uses the proved type sheafification in u+1.
  letI := SiteUniverse.types X.etaleTopology
  -- Local instance justification (proof-local temporary data): bind the genuine full-comma limits in the same u+1 universe.
  letI (P : X.totalᵒᵖ ⥤ Type (u + 1)) := SiteUniverse.rightKan (toFunctor f) P
  exact @RingedSite.Cocontinuous.toRingedTopos.{u + 1, u, u + 1, u, u + 1}
    (commEtaleRingedSiteLift X) (commEtaleRingedSiteLift Y) (toFunctor f)
    inferInstance inferInstance (fun P => SiteUniverse.rightKan (toFunctor f) P)
    inferInstance inferInstance (etaleInverseCoefficientLift f)

/-- Étale module direct image in the canonical lifted ringed-site presentation. -/
def moduleDirectImageLift {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    EtaleModulesLift X ⥤ EtaleModulesLift Y :=
  (moduleDirectImageToposHomLift f).modulePushforward

instance moduleDirectImageLift_additive {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    (moduleDirectImageLift f).Additive :=
  RingedSite.ToposHom.modulePushforward_additive (moduleDirectImageToposHomLift f)

/-- Higher direct image on the genuine canonical lifted module categories. -/
def moduleHigherDirectImageFunctorLift {X Y : GroupoidsOver S} (f : X ⟶ Y) (i : ℕ) :
    EtaleModulesLift X ⥤ EtaleModulesLift Y :=
  (moduleDirectImageLift f).rightDerived i

/-- An original-u input is explicitly lifted BEFORE the canonical higher
direct image; its output remains in u+1 and is never shrunk. -/
def moduleHigherDirectImageLift {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (F : etaleModules X) (i : ℕ) : EtaleModulesLift Y :=
  (moduleHigherDirectImageFunctorLift f i).obj ((ModuleUniverseComparison.lift X).obj F)

end AlgebraicGeometry.GroupoidsOver
