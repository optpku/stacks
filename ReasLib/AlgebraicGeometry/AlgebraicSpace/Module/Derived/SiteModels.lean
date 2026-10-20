module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Closure
public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent.ChaoticClosure
public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent.ChaoticCohomology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.CommRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.AffineEtale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.UniverseLift

/-!
# Affine étale and chaotic presentations of derived quasi-coherence

The affine étale ringed site, the same affine site with the chaotic topology,
and the comparison-map category `QC` give presentations of derived modules with
quasi-coherent cohomology.

The enlarged ambient categories use module universe `u + 1` and coefficient
rings in `CommRingCat.{u + 1}`. Each presentation requires every cohomology
module sheaf to have `u`-small sections on every object of its site. Thus all
presentations have the same effective module universe `u` as the native category
`DerivedQCoh X`; the lifted small étale presentation permits comparison between them.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty
open SheafOfModules.RingedSite
open RingedSite.Hom
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- The affine étale global-sections presheaf, with rings lifted to `CommRingCat.{u + 1}`. -/
def affineEtaleCommStructurePresheafLift {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (affineEtaleSite X)ᵒᵖ ⥤ CommRingCat.{u + 1} :=
  AffineEtale.commStructurePresheaf X ⋙ CommRingCat.universeLift.{u, u + 1}

/-- The lifted affine étale presheaf is restriction of the lifted small étale commutative
structure sheaf. -/
theorem affineEtaleCommStructurePresheafLift_eq {S : Scheme.{u}} (X : AlgebraicSpace S) :
    affineEtaleCommStructurePresheafLift X =
      (affineEtaleInclusion X).op ⋙ (commStructureSheafLift X).obj := sorry

/-- The lifted affine étale global-sections presheaf is a sheaf for the affine étale
topology. -/
theorem affineEtaleCommStructurePresheafLift_isSheaf {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    Presheaf.IsSheaf (affineEtaleTopology X)
      (affineEtaleCommStructurePresheafLift X) := sorry

/-- Commutative-ring-valued sheaf composition exists on the affine étale topology in
universe `u + 1`. -/
instance affineEtaleTopology_hasSheafCompose_commRing_succ {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    (affineEtaleTopology X).HasSheafCompose
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := sorry

/-- The dense affine inclusion is a morphism of sites. -/
instance affineEtaleInclusionIsMorphismOfSites {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsMorphismOfSites (affineEtaleTopology X) (smallEtaleTopology X)
      (affineEtaleInclusion X) := sorry

/-- The lifted commutative structure sheaf on the affine étale site, obtained by continuous
pushforward of the lifted small étale commutative structure sheaf. -/
noncomputable def affineEtaleCommStructureSheafLift {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    Sheaf (affineEtaleTopology X) CommRingCat.{u + 1} :=
  ((affineEtaleInclusion X).sheafPushforwardContinuous CommRingCat.{u + 1}
    (affineEtaleTopology X) (smallEtaleTopology X)).obj
    (commStructureSheafLift X)

/-- The underlying presheaf of the lifted affine étale structure sheaf is the lifted
affine global-sections presheaf. -/
theorem affineEtaleCommStructureSheafLift_obj {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (affineEtaleCommStructureSheafLift X).obj =
      affineEtaleCommStructurePresheafLift X := sorry

/-- The affine étale site of an algebraic space with its universe-pinned commutative
structure sheaf. -/
noncomputable abbrev affineEtaleRingedSiteLift {S : Scheme.{u}} (X : AlgebraicSpace S) :
    RingedSite.{u + 1, u, u + 1} :=
  RingedSite.ofCommRingSheaf (affineEtaleTopology X)
    (affineEtaleCommStructureSheafLift X)

/-- The dense affine inclusion as a morphism from the lifted small étale ringed site to
the lifted affine étale ringed site. -/
noncomputable def affineEtaleRingedSiteHom {S : Scheme.{u}} (X : AlgebraicSpace S) :
    RingedSite.Hom (commRingedSiteLift X) (affineEtaleRingedSiteLift X) where
  base := affineEtaleInclusion X
  structureSheafMap := 𝟙 _

/-- The base functor of the affine étale comparison is the affine étale inclusion. -/
theorem affineEtaleRingedSiteHom_base {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (affineEtaleRingedSiteHom X).base = affineEtaleInclusion X := sorry

/-- The structure sheaf on affine étale objects equipped with the chaotic topology. -/
noncomputable def affineChaoticStructureSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Sheaf (⊥ : GrothendieckTopology (affineEtaleSite X)) CommRingCat.{u + 1} :=
  ⟨affineEtaleCommStructurePresheafLift X, Presheaf.isSheaf_bot _⟩

/-- Commutative-ring-valued sheaf composition exists on the chaotic affine étale site in
universe `u + 1`. -/
instance affineChaotic_hasSheafCompose_commRing {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ((⊥ : GrothendieckTopology (affineEtaleSite X))).HasSheafCompose
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := sorry

/-- The affine étale site with the chaotic topology and its lifted commutative structure
sheaf. -/
noncomputable abbrev affineChaoticRingedSite {S : Scheme.{u}} (X : AlgebraicSpace S) :
    RingedSite.{u + 1, u, u + 1} :=
  RingedSite.ofCommRingSheaf
    (⊥ : GrothendieckTopology (affineEtaleSite X))
    (affineChaoticStructureSheaf X)

/-- The derived category of modules on the affine chaotic ringed site. -/
abbrev affineChaoticDerived {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  RingedSite.Hom.ModuleDerived.{u + 1} (affineChaoticRingedSite X)

/-- The underlying presheaf of the affine chaotic structure sheaf. -/
theorem affineChaoticStructureSheaf_obj {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (affineChaoticStructureSheaf X).obj = affineEtaleCommStructurePresheafLift X := sorry

/-- Restriction morphisms of the affine chaotic structure sheaf are flat. -/
instance affineChaoticStructureSheafFlat {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Presheaf.Restriction.Flat (affineChaoticStructureSheaf X).obj := sorry

/-- The identity functor is a morphism from the chaotic affine site to the affine étale
site. -/
instance affineTopologyIdentityIsMorphismOfSites {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsMorphismOfSites
      (⊥ : GrothendieckTopology (affineEtaleSite X))
      (affineEtaleTopology X) (𝟭 _) := sorry

/-- The identity-on-affines morphism from the affine étale ringed site to its chaotic
topology presentation. -/
noncomputable def affineTopologyRingedSiteHom {S : Scheme.{u}} (X : AlgebraicSpace S) :
    RingedSite.Hom (affineEtaleRingedSiteLift X) (affineChaoticRingedSite X) where
  base := 𝟭 _
  structureSheafMap := 𝟙 _

/-- Quasi-coherent cohomology with `u`-small sections on the lifted small étale site. -/
abbrev liftedProperty {S : Scheme.{u}} (X : AlgebraicSpace S) : ObjectProperty
    (RingedSite.Hom.ModuleDerived.{u + 1} (commRingedSiteLift X)) :=
  fun K ↦ (@DerivedCategory.cohomologyIn _ _ _
    (RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1} (commRingedSiteLift X))
    (SheafOfModules.isQuasicoherent.{u + 1, u, u + 1}
      (ringSheaf.{u + 1, u, u + 1} (smallEtaleTopology X) (commStructureSheafLift X))) K) ∧
    ∀ (n : ℤ) (U : (smallEtaleSite X)ᵒᵖ),
      Small.{u} (((@DerivedCategory.homologyFunctor
        (RingedSite.ModuleCat.{u + 1} (commRingedSiteLift X)) _ _
        (moduleCat_hasDerivedCategory.{u + 1} (commRingedSiteLift X)) n).obj K).val.obj U)

/-- The lifted small étale presentation with quasi-coherent, sectionwise `u`-small
cohomology. -/
abbrev Lifted {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  (liftedProperty X).FullSubcategory

/-- Quasi-coherent cohomology with `u`-small sections on the affine étale site. -/
abbrev affineEtaleProperty {S : Scheme.{u}} (X : AlgebraicSpace S) : ObjectProperty
    (RingedSite.Hom.ModuleDerived.{u + 1} (affineEtaleRingedSiteLift X)) :=
  fun K ↦ (@DerivedCategory.cohomologyIn _ _ _
    (RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1}
      (affineEtaleRingedSiteLift X))
    (SheafOfModules.isQuasicoherent.{u + 1, u, u + 1}
      (ringSheaf.{u + 1, u, u + 1} (affineEtaleTopology X)
        (affineEtaleCommStructureSheafLift X))) K) ∧
    ∀ (n : ℤ) (U : (affineEtaleSite X)ᵒᵖ),
      Small.{u} (((@DerivedCategory.homologyFunctor
        (RingedSite.ModuleCat.{u + 1} (affineEtaleRingedSiteLift X)) _ _
        (moduleCat_hasDerivedCategory.{u + 1} (affineEtaleRingedSiteLift X)) n).obj K).val.obj U)

/-- The affine étale presentation with quasi-coherent, sectionwise `u`-small cohomology. -/
abbrev AffineEtale {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  (affineEtaleProperty X).FullSubcategory

/-- Quasi-coherent cohomology with `u`-small sections on the affine chaotic site. -/
abbrev affineProperty {S : Scheme.{u}} (X : AlgebraicSpace S) : ObjectProperty
    (affineChaoticDerived X) :=
  fun K ↦ (@DerivedCategory.cohomologyIn _ _ _
    (RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1}
      (affineChaoticRingedSite X))
    (SheafOfModules.isQuasicoherent.{u + 1, u, u + 1}
      (ringSheaf.{u + 1, u, u + 1}
        (⊥ : GrothendieckTopology (affineEtaleSite X))
        (affineChaoticStructureSheaf X))) K) ∧
    ∀ (n : ℤ) (U : (affineEtaleSite X)ᵒᵖ),
      Small.{u} (((@DerivedCategory.homologyFunctor
        (RingedSite.ModuleCat.{u + 1} (affineChaoticRingedSite X)) _ _
        (moduleCat_hasDerivedCategory.{u + 1} (affineChaoticRingedSite X)) n).obj K).val.obj U)

/-- The affine chaotic presentation with quasi-coherent, sectionwise `u`-small cohomology. -/
abbrev Affine {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  (affineProperty X).FullSubcategory

/-- Comparison-map quasi-coherence with sectionwise `u`-small cohomology on the affine
chaotic site. -/
abbrev affineQCProperty {S : Scheme.{u}} (X : AlgebraicSpace S) : ObjectProperty
    (affineChaoticDerived X) :=
  fun K ↦ ModulesOnCategory.Chaotic.isQuasiCoherent.{u + 1, u, u}
    (affineChaoticStructureSheaf X) K ∧
    ∀ (n : ℤ) (U : (affineEtaleSite X)ᵒᵖ),
      Small.{u} (((@DerivedCategory.homologyFunctor
        (RingedSite.ModuleCat.{u + 1} (affineChaoticRingedSite X)) _ _
        (moduleCat_hasDerivedCategory.{u + 1} (affineChaoticRingedSite X)) n).obj K).val.obj U)

/-- The comparison-map presentation `QC(X_affine, 𝒪)` with sectionwise `u`-small cohomology. -/
abbrev AffineQC {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  (affineQCProperty X).FullSubcategory

/-- Quasi-coherent cohomology is a triangulated property on `D(𝒪_X)`. -/
instance isTriangulated {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (derivedQuasiCoherentModuleProperty X).IsTriangulated := sorry

/-- Quasi-coherent, sectionwise `u`-small cohomology is a triangulated property on the
lifted small étale model. -/
instance liftedIsTriangulated {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (liftedProperty X).IsTriangulated := sorry

/-- Quasi-coherent, sectionwise `u`-small cohomology is a triangulated property on the
affine étale model. -/
instance affineEtaleIsTriangulated {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (affineEtaleProperty X).IsTriangulated := sorry

/-- Quasi-coherent, sectionwise `u`-small cohomology is a triangulated property on the
affine chaotic model. -/
instance affineIsTriangulated {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (affineProperty X).IsTriangulated := sorry

/-- Comparison-map quasi-coherence with sectionwise `u`-small cohomology is a triangulated
property on the affine chaotic model. -/
instance affineQCIsTriangulated {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (affineQCProperty X).IsTriangulated := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
