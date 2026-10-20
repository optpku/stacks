/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Closure
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.ModuleEquivalence
public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent.ChaoticCohomology
public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent.ChaoticClosure
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.CommRing
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.SmallAffine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.GlobalSections

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty
open SheafOfModules.RingedSite
open RingedSite.Hom
open scoped TopCat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- The structure sheaf on the opens of `X`, transported from the lifted commutative-ring
presentation of the small Zariski site. -/
noncomputable def liftedOpensRingSheaf (X : Scheme.{u}) :
    Sheaf (Opens.grothendieckTopology (X : TopCat)) RingCat.{u + 1} :=
  (Scheme.smallZariskiSheafEquiv X RingCat.{u + 1}).functor.obj
    (ringSheaf.{u + 1, u, u + 1} (SmallStandardTopology.topology .zariski X)
      (AssociatedModule.smallCommStructureSheaf .zariski X))

/-- The lifted ring sheaf on the opens is obtained by the canonical Zariski sheaf equivalence. -/
theorem liftedOpensRingSheaf_def (X : Scheme.{u}) :
    liftedOpensRingSheaf X =
      (Scheme.smallZariskiSheafEquiv X RingCat.{u + 1}).functor.obj
        (ringSheaf.{u + 1, u, u + 1} (SmallStandardTopology.topology .zariski X)
          (AssociatedModule.smallCommStructureSheaf .zariski X)) := sorry

/-- The opens of `X` equipped with the lifted structure sheaf used by all four presentations. -/
noncomputable abbrev liftedOpensRingedSite (X : Scheme.{u}) : RingedSite.{u, u, u + 1} :=
  RingedSite.ofRingSheaf (Opens.grothendieckTopology (X : TopCat))
    (liftedOpensRingSheaf X)

/-- The small Zariski site of a scheme with its universe-pinned commutative structure sheaf. -/
noncomputable abbrev smallZariskiRingedSite (X : Scheme.{u}) :
    RingedSite.{u + 1, u, u + 1} :=
  RingedSite.ofCommRingSheaf
    (SmallStandardTopology.topology .zariski X)
    (AssociatedModule.smallCommStructureSheaf .zariski X)

/-- The canonical functor from opens is a morphism of sites for the lifted presentations. -/
theorem liftedSmallZariskiOpenFunctorIsMorphismOfSites (X : Scheme.{u}) :
    IsMorphismOfSites
      (liftedOpensRingedSite X).siteTopology
      (smallZariskiRingedSite X).siteTopology
      (Scheme.smallZariskiOpenFunctor X) := sorry

/-- The canonical comparison from the lifted small Zariski ringed site to the lifted opens
presentation. -/
noncomputable def liftedSmallZariskiRingedSiteHom (X : Scheme.{u}) :
    RingedSite.Hom (smallZariskiRingedSite X) (liftedOpensRingedSite X) where
  base := Scheme.smallZariskiOpenFunctor X
  isMorphismOfSites := liftedSmallZariskiOpenFunctorIsMorphismOfSites X
  structureSheafMap := 𝟙 _

/-- The base functor of the lifted comparison is the canonical functor from opens. -/
theorem liftedSmallZariskiRingedSiteHom_base (X : Scheme.{u}) :
    (liftedSmallZariskiRingedSiteHom X).base = Scheme.smallZariskiOpenFunctor X := sorry

/-- The quasi-coherent cohomology property on the lifted opens presentation. -/
abbrev opensProperty (X : Scheme.{u}) : ObjectProperty
    (RingedSite.Hom.ModuleDerived.{u + 1} (liftedOpensRingedSite X)) :=
  @DerivedCategory.cohomologyIn _ _ _
    (RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1} (liftedOpensRingedSite X))
    (SheafOfModules.isQuasicoherent.{u + 1, u, u} (liftedOpensRingSheaf X))

/-- The common-universe opens presentation of `D_QCoh(𝒪_X)`. -/
abbrev Opens (X : Scheme.{u}) := (opensProperty X).FullSubcategory

/-- The quasi-coherent cohomology property on the small Zariski derived category. -/
abbrev smallZariskiProperty (X : Scheme.{u}) : ObjectProperty
    (RingedSite.Hom.ModuleDerived.{u + 1} (smallZariskiRingedSite X)) :=
  @DerivedCategory.cohomologyIn _ _ _
    (RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1}
      (smallZariskiRingedSite X))
    (SheafOfModules.isQuasicoherent.{u + 1, u, u + 1}
      (ringSheaf.{u + 1, u, u + 1}
        (SmallStandardTopology.topology .zariski X)
        (AssociatedModule.smallCommStructureSheaf .zariski X)))

/-- The small-Zariski presentation of derived modules with quasi-coherent cohomology. -/
abbrev SmallZariski (X : Scheme.{u}) := (smallZariskiProperty X).FullSubcategory

/-- The affine global-functions presheaf, with its rings lifted to the small-site universe. -/
def affineCommStructurePresheaf (X : Scheme.{u}) :
    (SmallStandardTopology.Affine.site .zariski X)ᵒᵖ ⥤ CommRingCat.{u + 1} :=
  (SmallStandardTopology.Affine.inclusion .zariski X).op ⋙
    (AssociatedModule.smallCommStructureSheaf .zariski X).obj

/-- The lifted affine global-functions presheaf is the canonical presheaf of the affine site. -/
theorem affineCommStructurePresheaf_def (X : Scheme.{u}) :
    affineCommStructurePresheaf X =
      Scheme.Over.commStructurePresheaf
        (SmallStandardTopology.Affine.toOver .zariski X) := sorry

/-- The lifted affine global-functions presheaf is a sheaf for the affine Zariski topology. -/
theorem affineCommStructurePresheaf_isSheaf (X : Scheme.{u}) :
    Presheaf.IsSheaf (SmallStandardTopology.Affine.topology .zariski X)
      (affineCommStructurePresheaf X) := sorry

/-- The lifted commutative structure sheaf on the small affine Zariski site. -/
noncomputable def affineZariskiStructureSheaf (X : Scheme.{u}) :
    Sheaf (SmallStandardTopology.Affine.topology .zariski X)
      CommRingCat.{u + 1} :=
  ((SmallStandardTopology.Affine.inclusion .zariski X).sheafPushforwardContinuous
    CommRingCat.{u + 1} (SmallStandardTopology.Affine.topology .zariski X)
    (SmallStandardTopology.topology .zariski X)).obj
      (AssociatedModule.smallCommStructureSheaf .zariski X)

/-- The affine Zariski site of a scheme with its universe-pinned commutative structure sheaf. -/
noncomputable abbrev affineZariskiRingedSite (X : Scheme.{u}) :
    RingedSite.{u + 1, u, u + 1} :=
  RingedSite.ofCommRingSheaf
    (SmallStandardTopology.Affine.topology .zariski X)
    (affineZariskiStructureSheaf X)

/-- The underlying presheaf of the lifted affine Zariski structure sheaf. -/
theorem affineZariskiStructureSheaf_obj (X : Scheme.{u}) :
    (affineZariskiStructureSheaf X).obj = affineCommStructurePresheaf X := sorry

/-- The dense affine inclusion is a morphism from the affine Zariski site to the small
Zariski site. -/
instance affineInclusionIsMorphismOfSites (X : Scheme.{u}) :
    IsMorphismOfSites
      (SmallStandardTopology.Affine.topology .zariski X)
      (SmallStandardTopology.topology .zariski X)
      (SmallStandardTopology.Affine.inclusion .zariski X) := sorry

/-- The dense affine inclusion as a morphism from the affine Zariski ringed site to the
small Zariski ringed site. -/
noncomputable def affineZariskiRingedSiteHom (X : Scheme.{u}) :
    RingedSite.Hom (smallZariskiRingedSite X) (affineZariskiRingedSite X) where
  base := SmallStandardTopology.Affine.inclusion .zariski X
  structureSheafMap := 𝟙 _

/-- The structure sheaf on affine opens equipped with the chaotic topology. -/
noncomputable def affineChaoticStructureSheaf (X : Scheme.{u}) :
    Sheaf (⊥ : GrothendieckTopology
      (SmallStandardTopology.Affine.site .zariski X)) CommRingCat.{u + 1} :=
  ⟨affineCommStructurePresheaf X, Presheaf.isSheaf_bot _⟩

/-- The affine site with the chaotic topology and its lifted commutative structure sheaf. -/
noncomputable abbrev affineChaoticRingedSite (X : Scheme.{u}) :
    RingedSite.{u + 1, u, u + 1} :=
  RingedSite.ofCommRingSheaf
    (⊥ : GrothendieckTopology (SmallStandardTopology.Affine.site .zariski X))
    (affineChaoticStructureSheaf X)

/-- The derived category of modules on the affine chaotic ringed site. -/
abbrev affineChaoticDerived (X : Scheme.{u}) :=
  RingedSite.Hom.ModuleDerived.{u + 1} (affineChaoticRingedSite X)

/-- The underlying presheaf of the affine chaotic structure sheaf. -/
theorem affineChaoticStructureSheaf_obj (X : Scheme.{u}) :
    (affineChaoticStructureSheaf X).obj = affineCommStructurePresheaf X := sorry

/-- Restriction morphisms of the affine chaotic structure sheaf are flat. -/
instance affineChaoticStructureSheafFlat (X : Scheme.{u}) :
    Presheaf.Restriction.Flat (affineChaoticStructureSheaf X).obj := sorry

/-- The identity functor is a morphism from the chaotic affine site to the affine Zariski
site. -/
instance affineTopologyIdentityIsMorphismOfSites (X : Scheme.{u}) :
    IsMorphismOfSites
      (⊥ : GrothendieckTopology (SmallStandardTopology.Affine.site .zariski X))
      (SmallStandardTopology.Affine.topology .zariski X) (𝟭 _) := sorry

/-- The identity-on-affines morphism from the affine Zariski ringed site to its chaotic
topology presentation. -/
noncomputable def affineTopologyRingedSiteHom (X : Scheme.{u}) :
    RingedSite.Hom (affineZariskiRingedSite X) (affineChaoticRingedSite X) where
  base := 𝟭 _
  structureSheafMap := 𝟙 _

/-- The quasi-coherent cohomology property on the affine Zariski derived category. -/
abbrev affineZariskiProperty (X : Scheme.{u}) : ObjectProperty
    (RingedSite.Hom.ModuleDerived.{u + 1} (affineZariskiRingedSite X)) :=
  @DerivedCategory.cohomologyIn _ _ _
    (RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1}
      (affineZariskiRingedSite X))
    (SheafOfModules.isQuasicoherent.{u + 1, u, u + 1}
      (ringSheaf.{u + 1, u, u + 1}
        (SmallStandardTopology.Affine.topology .zariski X)
        (affineZariskiStructureSheaf X)))

/-- The affine-Zariski presentation of derived modules with quasi-coherent cohomology. -/
abbrev AffineZariski (X : Scheme.{u}) := (affineZariskiProperty X).FullSubcategory

/-- The quasi-coherent cohomology property on the affine chaotic derived category. -/
abbrev affineProperty (X : Scheme.{u}) : ObjectProperty
    (affineChaoticDerived X) :=
  @DerivedCategory.cohomologyIn _ _ _
    (RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1}
      (affineChaoticRingedSite X))
    (SheafOfModules.isQuasicoherent.{u + 1, u, u + 1}
      (ringSheaf.{u + 1, u, u + 1}
        (⊥ : GrothendieckTopology
          (SmallStandardTopology.Affine.site .zariski X))
        (affineChaoticStructureSheaf X)))

/-- The affine-chaotic presentation of derived modules with quasi-coherent cohomology. -/
abbrev Affine (X : Scheme.{u}) := (affineProperty X).FullSubcategory

/-- The comparison-map quasi-coherence property on the affine chaotic derived category. -/
abbrev affineQCProperty (X : Scheme.{u}) : ObjectProperty
    (affineChaoticDerived X) :=
  ModulesOnCategory.Chaotic.isQuasiCoherent.{u + 1, u, u}
    (affineChaoticStructureSheaf X)

/-- The comparison-map presentation `QC(X_affine, 𝒪)` on the affine chaotic site. -/
abbrev AffineQC (X : Scheme.{u}) := (affineQCProperty X).FullSubcategory

/-- Quasi-coherent cohomology is a triangulated property on `D(𝒪_X)`. -/
instance isTriangulated (X : Scheme.{u}) :
    (DerivedCategory.cohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).IsTriangulated := sorry

/-- Quasi-coherent cohomology is a triangulated property on the lifted opens model. -/
instance opensIsTriangulated (X : Scheme.{u}) :
    (opensProperty X).IsTriangulated := sorry

/-- Quasi-coherent cohomology is a triangulated property on the small Zariski model. -/
instance smallZariskiIsTriangulated (X : Scheme.{u}) :
    (smallZariskiProperty X).IsTriangulated := sorry

/-- Quasi-coherent cohomology is a triangulated property on the affine Zariski model. -/
instance affineZariskiIsTriangulated (X : Scheme.{u}) :
    (affineZariskiProperty X).IsTriangulated := sorry

/-- Quasi-coherent cohomology is a triangulated property on the affine chaotic model. -/
instance affineIsTriangulated (X : Scheme.{u}) :
    (affineProperty X).IsTriangulated := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
