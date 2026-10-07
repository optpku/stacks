module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.AffineOver.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.SiteModels
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.Continuous
public import ReasLib.CategoryTheory.Sites.AlmostCocontinuous.Exactness
public import ReasLib.CategoryTheory.Sites.Chaotic

/-!
# Restriction from all affine schemes to affine opens

This module constructs continuous restriction from the chaotic category of all affine schemes
over a scheme to its chaotic category of affine opens, together with its derived functor.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.ObjectProperty
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- The affine-open inclusion preserves identity morphisms. -/
theorem smallAffineZariskiToAffineOver_map_id (S : Scheme.{u})
    (U : SmallStandardTopology.Affine.site .zariski S) :
    (Scheme.AffineOver.homMk
        (S.homOfLE
          ((CategoryTheory.Cat.ObjULift.down S.smallAffineZariskiSite).map (𝟙 U)).hom.le)
        (S.homOfLE_ι _) :
      Scheme.AffineOver.mk U.down.obj U.down.property U.down.obj.ι ⟶
        Scheme.AffineOver.mk U.down.obj U.down.property U.down.obj.ι) =
      𝟙 (Scheme.AffineOver.mk U.down.obj U.down.property U.down.obj.ι) := sorry

/-- The affine-open inclusion preserves composition of morphisms. -/
theorem smallAffineZariskiToAffineOver_map_comp (S : Scheme.{u})
    {U V W : SmallStandardTopology.Affine.site .zariski S}
    (f : U ⟶ V) (g : V ⟶ W) :
    (Scheme.AffineOver.homMk
        (S.homOfLE
          ((CategoryTheory.Cat.ObjULift.down S.smallAffineZariskiSite).map (f ≫ g)).hom.le)
        (S.homOfLE_ι _) :
      Scheme.AffineOver.mk U.down.obj U.down.property U.down.obj.ι ⟶
        Scheme.AffineOver.mk W.down.obj W.down.property W.down.obj.ι) =
      (Scheme.AffineOver.homMk
          (S.homOfLE
            ((CategoryTheory.Cat.ObjULift.down S.smallAffineZariskiSite).map f).hom.le)
          (S.homOfLE_ι _) :
        Scheme.AffineOver.mk U.down.obj U.down.property U.down.obj.ι ⟶
          Scheme.AffineOver.mk V.down.obj V.down.property V.down.obj.ι) ≫
        (Scheme.AffineOver.homMk
          (S.homOfLE
            ((CategoryTheory.Cat.ObjULift.down S.smallAffineZariskiSite).map g).hom.le)
          (S.homOfLE_ι _) :
        Scheme.AffineOver.mk V.down.obj V.down.property V.down.obj.ι ⟶
          Scheme.AffineOver.mk W.down.obj W.down.property W.down.obj.ι) := sorry

/-- The inclusion of affine opens among all affine schemes over `S`. -/
def smallAffineZariskiToAffineOver (S : Scheme.{u}) :
    SmallStandardTopology.Affine.site .zariski S ⥤ S.AffineOver where
  obj U := Scheme.AffineOver.mk U.down.obj U.down.property U.down.obj.ι
  map f := Scheme.AffineOver.homMk
    (S.homOfLE ((CategoryTheory.Cat.ObjULift.down S.smallAffineZariskiSite).map f).hom.le)
    (S.homOfLE_ι _)
  map_id := smallAffineZariskiToAffineOver_map_id S
  map_comp := smallAffineZariskiToAffineOver_map_comp S

/-- Forgetting the affine-open inclusion recovers the standard functor to schemes over `S`. -/
theorem smallAffineZariskiToAffineOver_forget (S : Scheme.{u}) :
    smallAffineZariskiToAffineOver S ⋙ Scheme.AffineOver.forget S =
      SmallStandardTopology.Affine.toOver .zariski S := sorry

/-- The identity maps on the rings of affine opens are natural with respect to restriction. -/
theorem affineOverRestrictionStructureSheafMap_naturality (S : Scheme.{u})
    {U V : (SmallStandardTopology.Affine.site .zariski S)ᵒᵖ} (f : U ⟶ V) :
    (affineChaoticStructureSheaf S).obj.map f ≫
        (𝟙 _ : (affineChaoticStructureSheaf S).obj.obj V ⟶
          (((smallAffineZariskiToAffineOver S).sheafPushforwardContinuous
            CommRingCat.{u + 1}
            (⊥ : GrothendieckTopology (SmallStandardTopology.Affine.site .zariski S))
            (⊥ : GrothendieckTopology S.AffineOver)).obj
              (affineOverChaoticStructureSheaf S)).obj.obj V) =
      (𝟙 _ : (affineChaoticStructureSheaf S).obj.obj U ⟶
        (((smallAffineZariskiToAffineOver S).sheafPushforwardContinuous
          CommRingCat.{u + 1}
          (⊥ : GrothendieckTopology (SmallStandardTopology.Affine.site .zariski S))
          (⊥ : GrothendieckTopology S.AffineOver)).obj
            (affineOverChaoticStructureSheaf S)).obj.obj U) ≫
        (((smallAffineZariskiToAffineOver S).sheafPushforwardContinuous
          CommRingCat.{u + 1}
          (⊥ : GrothendieckTopology (SmallStandardTopology.Affine.site .zariski S))
          (⊥ : GrothendieckTopology S.AffineOver)).obj
            (affineOverChaoticStructureSheaf S)).obj.map f := sorry

/-- The direct-image-form map from the affine-open structure sheaf to the restriction of the
all-affine structure sheaf. -/
def affineOverRestrictionStructureSheafMap (S : Scheme.{u}) :
    affineChaoticStructureSheaf S ⟶
      ((smallAffineZariskiToAffineOver S).sheafPushforwardContinuous
        CommRingCat.{u + 1}
        (⊥ : GrothendieckTopology (SmallStandardTopology.Affine.site .zariski S))
        (⊥ : GrothendieckTopology S.AffineOver)).obj
          (affineOverChaoticStructureSheaf S) :=
  ⟨{ app := fun _ ↦ 𝟙 _
     naturality := fun _ _ f ↦
       affineOverRestrictionStructureSheafMap_naturality S f }⟩

/-- Restriction of module sheaves from all affine schemes over `S` to its affine opens. -/
noncomputable abbrev affineOverModuleRestriction (S : Scheme.{u}) :
    ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
        (⊥ : GrothendieckTopology S.AffineOver)
        (affineOverChaoticStructureSheaf S) ⥤
      ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
        (⊥ : GrothendieckTopology (SmallStandardTopology.Affine.site .zariski S))
        (affineChaoticStructureSheaf S) :=
  SheafOfModules.RingedSite.modulePushforward.{u + 1, u, u + 1, u, u + 1, u + 1}
    (smallAffineZariskiToAffineOver S)
    (affineOverRestrictionStructureSheafMap S)

/-- Restriction from all affine schemes to affine opens, bundled as an exact functor. -/
noncomputable def affineOverModuleRestrictionExact (S : Scheme.{u}) :
    ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
        (⊥ : GrothendieckTopology S.AffineOver)
        (affineOverChaoticStructureSheaf S) ⥤ₑ
      ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
        (⊥ : GrothendieckTopology (SmallStandardTopology.Affine.site .zariski S))
        (affineChaoticStructureSheaf S) :=
  CategoryTheory.Functor.IsAlmostCocontinuous.sheafOfModulesPushforwardExactFunctor.{u + 1,
    u + 1, u, u, u + 1, u + 1}
    (smallAffineZariskiToAffineOver S)
    (ringSheaf.{u + 1, u, u + 1}
      (⊥ : GrothendieckTopology (SmallStandardTopology.Affine.site .zariski S))
      (affineChaoticStructureSheaf S))
    (ringSheaf.{u + 1, u, u + 1} (⊥ : GrothendieckTopology S.AffineOver)
      (affineOverChaoticStructureSheaf S))
    (SheafOfModules.RingedSite.moduleStructureMap.{u + 1, u, u + 1, u, u + 1}
      (smallAffineZariskiToAffineOver S)
      (affineOverRestrictionStructureSheafMap S))

/-- The derived restriction from all affine schemes over `S` to its affine opens. -/
noncomputable abbrev affineOverDerivedRestriction (S : Scheme.{u}) :
    RingedSite.Hom.ModuleDerived.{u + 1}
        (RingedSite.ofCommRingSheaf (⊥ : GrothendieckTopology S.AffineOver)
          (affineOverChaoticStructureSheaf S)) ⥤
      RingedSite.Hom.ModuleDerived.{u + 1}
        (RingedSite.ofCommRingSheaf
          (⊥ : GrothendieckTopology (SmallStandardTopology.Affine.site .zariski S))
          (affineChaoticStructureSheaf S)) :=
  @Functor.mapDerivedCategory
    (ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
      (⊥ : GrothendieckTopology S.AffineOver)
      (affineOverChaoticStructureSheaf S)) inferInstance inferInstance
    (RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1, u + 1, u, u + 1}
      (RingedSite.ofCommRingSheaf (⊥ : GrothendieckTopology S.AffineOver)
        (affineOverChaoticStructureSheaf S)))
    (ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
      (⊥ : GrothendieckTopology (SmallStandardTopology.Affine.site .zariski S))
      (affineChaoticStructureSheaf S)) inferInstance inferInstance
    (RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1, u + 1, u, u + 1}
      (RingedSite.ofCommRingSheaf
        (⊥ : GrothendieckTopology (SmallStandardTopology.Affine.site .zariski S))
        (affineChaoticStructureSheaf S)))
    (affineOverModuleRestrictionExact S).obj inferInstance inferInstance inferInstance

/-- Derived restriction identifies the base-change comparison on an affine open with the
corresponding comparison on the category of all affine schemes over `S`. -/
theorem affineOverDerivedRestriction_comparison (S : Scheme.{u})
    (K : RingedSite.Hom.ModuleDerived.{u + 1}
      (RingedSite.ofCommRingSheaf (⊥ : GrothendieckTopology S.AffineOver)
        (affineOverChaoticStructureSheaf S)))
    {U V : SmallStandardTopology.Affine.site .zariski S} (f : U ⟶ V) :
    IsIso ((CategoryTheory.ModulesOnCategory.chaoticComparison.{u + 1, u, u}
        (affineChaoticStructureSheaf S) f).app
      ((affineOverDerivedRestriction S).obj K)) ↔
      IsIso ((CategoryTheory.ModulesOnCategory.chaoticComparison.{u + 1, u, u}
        (affineOverChaoticStructureSheaf S)
        ((smallAffineZariskiToAffineOver S).map f)).app K) := sorry

/-- Derived restriction takes comparison-quasi-coherent objects on all affine schemes over `S`
to comparison-quasi-coherent objects on affine opens. -/
theorem affineOverRestriction_mapsTo (S : Scheme.{u}) :
    ∀ K : RingedSite.Hom.ModuleDerived.{u + 1}
        (RingedSite.ofCommRingSheaf (⊥ : GrothendieckTopology S.AffineOver)
          (affineOverChaoticStructureSheaf S)),
      CategoryTheory.ModulesOnCategory.Chaotic.isQuasiCoherent.{u + 1, u, u}
          (affineOverChaoticStructureSheaf S) K →
        CategoryTheory.ModulesOnCategory.Chaotic.isQuasiCoherent.{u + 1, u, u}
          (affineChaoticStructureSheaf S)
          ((affineOverDerivedRestriction S).obj K) := sorry

namespace AffineOverQC

/-- Restriction from comparison-quasi-coherent derived modules on all affine schemes over `S`
to the corresponding category on affine opens. -/
noncomputable def restrictToAffine (S : Scheme.{u}) :
    AffineOverQC S ⥤ AffineQC S :=
  FullSubcategory.restrict (affineOverDerivedRestriction S)
    (affineOverRestriction_mapsTo S)

/-- Comparison-quasi-coherent derived modules on all affine schemes over `S` are determined by
their restriction to affine opens. -/
instance restrictToAffineIsEquivalence (S : Scheme.{u}) :
    (restrictToAffine S).IsEquivalence := sorry

end AffineOverQC

end AlgebraicGeometry.Scheme.DerivedQCoh
