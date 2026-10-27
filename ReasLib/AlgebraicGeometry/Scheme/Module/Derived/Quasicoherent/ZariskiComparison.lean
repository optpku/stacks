/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Sheafification
public import ReasLib.AlgebraicGeometry.Scheme.Sites.StructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.ModuleEquivalence
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Equivalence
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction

/-!
# Derived quasi-coherent comparison with the small Zariski site

The identity comparison on opens and the canonical maps on global sections identify
the quasi-coherent derived categories of a scheme and its small Zariski ringed site.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory Opposite
open CategoryTheory.Limits
open RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- Abelian-group-valued sheaf composition exists on the small Zariski topology of a scheme. -/
instance smallZariski_hasSheafCompose (X : Scheme.{u}) :
    X.smallZariskiTopology.HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  (smallZariskiOpenEquivalence X).symm.hasSheafCompose X.smallZariskiTopology
    (Opens.grothendieckTopology (X : TopCat)) (forget₂ RingCat AddCommGrpCat)

/-- Modules on the small Zariski ringed site have normal monomorphisms and epimorphisms,
finite products, kernels, and cokernels. -/
theorem zariskiModulesAbelian_axioms (X : Scheme.{u}) :
    IsNormalMonoCategory (SheafOfModules.{u} (Zariski.Small.structureSheaf X)) ∧
      IsNormalEpiCategory (SheafOfModules.{u} (Zariski.Small.structureSheaf X)) ∧
      CategoryTheory.Limits.HasFiniteProducts (SheafOfModules.{u} (Zariski.Small.structureSheaf X)) ∧
      CategoryTheory.Limits.HasKernels (SheafOfModules.{u} (Zariski.Small.structureSheaf X)) ∧
      CategoryTheory.Limits.HasCokernels (SheafOfModules.{u} (Zariski.Small.structureSheaf X)) := by
  letI := (smallZariskiOpenEquivalence X).symm.hasSheafify X.smallZariskiTopology
    (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat.{u}
  letI := GrothendieckTopology.WEqualsLocallyBijective.transport (A := AddCommGrpCat.{u})
    X.smallZariskiTopology
    (Opens.grothendieckTopology (X : TopCat)) (smallZariskiOpenFunctor X)
    (Functor.IsDenseSubsite.coverPreserving _ _ _)
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- The category of modules on the small Zariski ringed site of a scheme is abelian. -/
instance zariskiModulesAbelian (X : Scheme.{u}) :
    Abelian (SheafOfModules.{u} (Zariski.Small.structureSheaf X)) where
  toPreadditive := inferInstance
  toIsNormalMonoCategory := (zariskiModulesAbelian_axioms X).1
  toIsNormalEpiCategory := (zariskiModulesAbelian_axioms X).2.1
  has_finite_products := (zariskiModulesAbelian_axioms X).2.2.1
  has_kernels := (zariskiModulesAbelian_axioms X).2.2.2.1
  has_cokernels := (zariskiModulesAbelian_axioms X).2.2.2.2

/-- Modules on the transported small Zariski ringed site have normal monomorphisms and
epimorphisms, finite products, kernels, and cokernels. -/
theorem smallZariskiTransportedModulesAbelian_axioms (X : Scheme.{u}) :
    IsNormalMonoCategory (SheafOfModules.{u} (smallZariskiRingSheaf X)) ∧
      IsNormalEpiCategory (SheafOfModules.{u} (smallZariskiRingSheaf X)) ∧
      CategoryTheory.Limits.HasFiniteProducts (SheafOfModules.{u} (smallZariskiRingSheaf X)) ∧
      CategoryTheory.Limits.HasKernels (SheafOfModules.{u} (smallZariskiRingSheaf X)) ∧
      CategoryTheory.Limits.HasCokernels (SheafOfModules.{u} (smallZariskiRingSheaf X)) := by
  letI := (smallZariskiOpenEquivalence X).symm.hasSheafify X.smallZariskiTopology
    (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat.{u}
  letI := GrothendieckTopology.WEqualsLocallyBijective.transport (A := AddCommGrpCat.{u})
    X.smallZariskiTopology
    (Opens.grothendieckTopology (X : TopCat)) (smallZariskiOpenFunctor X)
    (Functor.IsDenseSubsite.coverPreserving _ _ _)
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- The category of modules on the transported small Zariski ringed site of a scheme is
abelian. -/
instance smallZariskiTransportedModulesAbelian (X : Scheme.{u}) :
    Abelian (SheafOfModules.{u} (smallZariskiRingSheaf X)) where
  toPreadditive := inferInstance
  toIsNormalMonoCategory := (smallZariskiTransportedModulesAbelian_axioms X).1
  toIsNormalEpiCategory := (smallZariskiTransportedModulesAbelian_axioms X).2.1
  has_finite_products := (smallZariskiTransportedModulesAbelian_axioms X).2.2.1
  has_kernels := (smallZariskiTransportedModulesAbelian_axioms X).2.2.2.1
  has_cokernels := (smallZariskiTransportedModulesAbelian_axioms X).2.2.2.2

/-- The standard derived-category structure on modules on the small Zariski ringed site. -/
instance instHasDerivedCategory_zariskiModules (X : Scheme.{u}) :
    HasDerivedCategory (SheafOfModules.{u} (Zariski.Small.structureSheaf X)) :=
  HasDerivedCategory.standard _

/-- The standard derived-category structure on modules on the transported small Zariski
ringed site. -/
instance instHasDerivedCategory_smallZariskiTransportedModules (X : Scheme.{u}) :
    HasDerivedCategory (SheafOfModules.{u} (smallZariskiRingSheaf X)) :=
  HasDerivedCategory.standard _

namespace DerivedQCoh

/-- The property that every cohomology sheaf of a derived module on the small Zariski
ringed site is quasi-coherent. -/
abbrev zariskiSiteProperty (X : Scheme.{u}) :
    ObjectProperty
      (DerivedCategory (SheafOfModules.{u} (Zariski.Small.structureSheaf X))) :=
  DerivedCategory.cohomologyIn
    (SheafOfModules.isQuasicoherent (Zariski.Small.structureSheaf X))

/-- The derived category of quasi-coherent modules on the small Zariski ringed site of `X`.
This is the domain of `ε^*` in the comparison of ringed sites
`(X_étale, 𝒪_étale) ⟶ (X_Zar, 𝒪_X)`. -/
abbrev ZariskiSite (X : Scheme.{u}) :=
  DerivedCategory.CohomologyIn
    (SheafOfModules.isQuasicoherent (Zariski.Small.structureSheaf X))

namespace ZariskiSite

/-- The inclusion of derived modules with quasi-coherent cohomology into `D(𝒪_Zar)`. -/
abbrev inclusion (X : Scheme.{u}) :
    ZariskiSite X ⥤
      DerivedCategory (SheafOfModules.{u} (Zariski.Small.structureSheaf X)) :=
  (zariskiSiteProperty X).ι

end ZariskiSite

/-- The open-range functor from the small Zariski site of `X` to its opens is a morphism of
sites. -/
instance smallZariskiRangeFunctor_isMorphismOfSites (X : Scheme.{u}) :
    IsMorphismOfSites X.smallZariskiTopology
      (Opens.grothendieckTopology (X : TopCat))
      (smallZariskiRangeFunctor X) := by
  change IsMorphismOfSites X.smallZariskiTopology
    (Opens.grothendieckTopology (X : TopCat)) (smallZariskiOpenEquivalence X).inverse
  letI := (smallZariskiOpenEquivalence X).isEquivalence_inverse
  refine { toIsContinuous := ⟨fun G ↦ ?_⟩, toRepresentablyFlat := inferInstance }
  exact (isSheaf_iff_isSheaf_of_type _ _).mp
    ((smallZariskiSheafEquiv X (Type (u + 1))).inverse.obj G).property

/-- The component of the structure-sheaf map of `opensToSmallZariski` at an open immersion
`U ⟶ X` is the identity on `Γ(X, U.opensRange)`, i.e. the unit/counit comparison of
`smallZariskiSheafEquiv` after evaluating at the open range. -/
noncomputable def opensToSmallZariskiStructureSheafHomApp (X : Scheme.{u})
    (U : X.smallZariskiSiteᵒᵖ) :
    (smallZariskiRingSheaf X).obj.obj U ⟶
      (((smallZariskiRangeFunctor X).sheafPushforwardContinuous RingCat.{u}
          X.smallZariskiTopology
          (Opens.grothendieckTopology (X : TopCat))).obj
        X.toRingedSpace.ringCatSheaf).obj.obj U :=
  𝟙 _

/-- The components of `opensToSmallZariskiStructureSheafHomApp` are identity maps on
`Γ(X, U.opensRange)`. -/
theorem opensToSmallZariskiStructureSheafHomApp_eq (X : Scheme.{u})
    (U : X.smallZariskiSiteᵒᵖ) :
    opensToSmallZariskiStructureSheafHomApp X U = 𝟙 _ := rfl

/-- The identity section maps on open ranges commute with restriction. -/
theorem opensToSmallZariskiStructureSheafHom_naturality (X : Scheme.{u})
    {U V : X.smallZariskiSiteᵒᵖ} (f : U ⟶ V) :
    (smallZariskiRingSheaf X).obj.map f ≫
        opensToSmallZariskiStructureSheafHomApp X V =
      opensToSmallZariskiStructureSheafHomApp X U ≫
        (((smallZariskiRangeFunctor X).sheafPushforwardContinuous RingCat.{u}
          X.smallZariskiTopology
          (Opens.grothendieckTopology (X : TopCat))).obj
          X.toRingedSpace.ringCatSheaf).obj.map f := rfl

/-- The natural transformation of structure sheaves whose components are identity maps on
`Γ(X, U.opensRange)`, the unit/counit comparison of `smallZariskiSheafEquiv`. -/
noncomputable def opensToSmallZariskiStructureSheafHom (X : Scheme.{u}) :
    smallZariskiRingSheaf X ⟶
      ((smallZariskiRangeFunctor X).sheafPushforwardContinuous RingCat.{u}
        X.smallZariskiTopology
        (Opens.grothendieckTopology (X : TopCat))).obj
        X.toRingedSpace.ringCatSheaf where
  hom.app := opensToSmallZariskiStructureSheafHomApp X
  hom.naturality := by
    intro U V f
    exact opensToSmallZariskiStructureSheafHom_naturality X f

/-- The inverse comparison from the opens ringed site of `X` to its transported small Zariski
ringed site, with base `smallZariskiRangeFunctor` and structure-sheaf map the unit/counit
comparison of `smallZariskiSheafEquiv`. -/
noncomputable def opensToSmallZariski (X : Scheme.{u}) :
    RingedSite.Hom (RingedSpace.opensRingedSite X.toRingedSpace)
      (smallZariskiRingedSite X) where
  base := smallZariskiRangeFunctor X
  isMorphismOfSites := smallZariskiRangeFunctor_isMorphismOfSites X
  structureSheafMap := opensToSmallZariskiStructureSheafHom X

/-- The base of `opensToSmallZariski` is the open-range functor. -/
theorem opensToSmallZariski_base (X : Scheme.{u}) :
    (opensToSmallZariski X).base = smallZariskiRangeFunctor X := rfl

/-- The structure-sheaf map of `opensToSmallZariski` is the unit/counit comparison of
`smallZariskiSheafEquiv`. -/
theorem opensToSmallZariski_structureSheafMap (X : Scheme.{u}) :
    (opensToSmallZariski X).structureSheafMap =
      opensToSmallZariskiStructureSheafHom X := rfl

/-- The opens-to-small-Zariski comparison is a ringed equivalence. -/
theorem opensToSmallZariski_isRingedEquivalence (X : Scheme.{u}) :
    (opensToSmallZariski X).IsRingedEquivalence := by
  letI : ((opensToSmallZariski X).sheafPushforwardContinuous
      (A := Type (u + 1))).IsEquivalence := by
    change (smallZariskiSheafEquiv X (Type (u + 1))).inverse.IsEquivalence
    infer_instance
  refine ⟨(opensToSmallZariski X).sheafAdjunctionContinuous
    |>.isEquivalence_left_of_isEquivalence_right, ?_⟩
  apply (ObjectProperty.isIso_hom_iff _).mp
  letI : ∀ U, IsIso ((opensToSmallZariski X).structureSheafMap.hom.app U) := by
    intro U
    change IsIso (𝟙 _)
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- An equivalence of categories preserves finite limits and finite colimits. -/
private theorem exact_of_isEquivalence
    {A : Type*} [Category A] {B : Type*} [Category B]
    (F : A ⥤ B) [hF : F.IsEquivalence] : exactFunctor A B F := by
  change PreservesFiniteLimits F ∧ PreservesFiniteColimits F
  exact ⟨inferInstance, inferInstance⟩

/-- Direct image from modules on the opens of a scheme to modules over the transported
small Zariski structure sheaf, bundled as an exact functor. -/
noncomputable def opensToSmallZariskiModulePushforward (X : Scheme.{u}) :
    SheafOfModules.{u} X.toRingedSpace.ringCatSheaf ⥤ₑ
      SheafOfModules.{u} (smallZariskiRingSheaf X) :=
  ⟨SheafOfModules.pushforward.{u} (opensToSmallZariskiStructureSheafHom X),
    by
      exact exact_of_isEquivalence _
        (hF := @RingedSite.Hom.modulePushforward_isEquivalence _ _
          (opensToSmallZariski X) (opensToSmallZariski_isRingedEquivalence X))⟩

/-- The component of the structure-sheaf map of `smallZariskiToZariskiSmall` at an open
immersion `U ⟶ X` is the canonical ring map `Γ(U, 𝒪_U) ⟶ Γ(X, U.opensRange)` obtained from
`IsOpenImmersion.ΓIsoTop`. -/
noncomputable def smallZariskiToZariskiSmallStructureSheafHomApp (X : Scheme.{u})
    (U : X.smallZariskiSiteᵒᵖ) :
    (Zariski.Small.structureSheaf X).obj.obj U ⟶
      (smallZariskiRingSheaf X).obj.obj U :=
  (forget₂ CommRingCat RingCat).map
    (@IsOpenImmersion.ΓIsoTop U.unop.left X U.unop.hom U.unop.prop).hom

/-- The components of `smallZariskiToZariskiSmallStructureSheafHomApp` are the maps
`Γ(U, 𝒪_U) ⟶ Γ(X, U.opensRange)` induced by `IsOpenImmersion.ΓIsoTop`. -/
theorem smallZariskiToZariskiSmallStructureSheafHomApp_eq (X : Scheme.{u})
    (U : X.smallZariskiSiteᵒᵖ) :
    smallZariskiToZariskiSmallStructureSheafHomApp X U =
      (forget₂ CommRingCat RingCat).map
        (@IsOpenImmersion.ΓIsoTop U.unop.left X U.unop.hom U.unop.prop).hom :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The canonical global-sections comparisons commute with restriction along
morphisms of the small Zariski site. -/
theorem smallZariskiToZariskiSmallStructureSheafHom_naturality (X : Scheme.{u})
    {U V : X.smallZariskiSiteᵒᵖ} (f : U ⟶ V) :
    (Zariski.Small.structureSheaf X).obj.map f ≫
        smallZariskiToZariskiSmallStructureSheafHomApp X V =
      smallZariskiToZariskiSmallStructureSheafHomApp X U ≫
        (smallZariskiRingSheaf X).obj.map f := by
  change (forget₂ CommRingCat RingCat).map f.unop.left.appTop ≫
      (forget₂ CommRingCat RingCat).map
        (@IsOpenImmersion.ΓIsoTop V.unop.left X V.unop.hom V.unop.prop).hom =
    (forget₂ CommRingCat RingCat).map
        (@IsOpenImmersion.ΓIsoTop U.unop.left X U.unop.hom U.unop.prop).hom ≫
      (forget₂ CommRingCat RingCat).map
        (X.presheaf.map ((smallZariskiRangeFunctor X).map f.unop).op)
  simp only [← Functor.map_comp]
  congr 1
  apply (cancel_mono
    (@IsOpenImmersion.ΓIsoTop V.unop.left X V.unop.hom V.unop.prop).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply (cancel_epi
    (@IsOpenImmersion.ΓIsoTop U.unop.left X U.unop.hom U.unop.prop).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  simp only [IsOpenImmersion.ΓIsoTop, Iso.trans_inv, Functor.mapIso_inv,
    Iso.op_inv, eqToIso.inv, eqToHom_op, Iso.symm_inv, Scheme.Hom.appIso_hom',
    Scheme.Hom.map_appLE]
  have hw : f.unop.left ≫ U.unop.hom = V.unop.hom :=
    Over.w ((smallZariskiForget X).map f.unop)
  simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, hw]
  exact (Scheme.Hom.map_appLE V.unop.hom _
    ((smallZariskiRangeFunctor X).map f.unop).op).symm

/-- The natural transformation of structure sheaves whose components are the
`Γ(U, 𝒪_U) ⟶ Γ(X, U.opensRange)` comparisons of `IsOpenImmersion.ΓIsoTop`. -/
noncomputable def smallZariskiToZariskiSmallStructureSheafHom (X : Scheme.{u}) :
    Zariski.Small.structureSheaf X ⟶ smallZariskiRingSheaf X where
  hom.app := smallZariskiToZariskiSmallStructureSheafHomApp X
  hom.naturality := by
    intro U V f
    exact smallZariskiToZariskiSmallStructureSheafHom_naturality X f

/-- The comparison from the transported small Zariski ringed site of `X` to
`Zariski.Small.ringedSite X`, with identity base functor and structure-sheaf map given by
the `Γ(U, 𝒪_U)` comparisons. -/
noncomputable def smallZariskiToZariskiSmall (X : Scheme.{u}) :
    RingedSite.Hom (smallZariskiRingedSite X) (Zariski.Small.ringedSite X) where
  base := 𝟭 _
  isMorphismOfSites := CategoryTheory.IsMorphismOfSites.id _
  structureSheafMap := smallZariskiToZariskiSmallStructureSheafHom X

/-- The base of `smallZariskiToZariskiSmall` is the identity on the small Zariski site. -/
theorem smallZariskiToZariskiSmall_base (X : Scheme.{u}) :
    (smallZariskiToZariskiSmall X).base = 𝟭 X.smallZariskiSite := rfl

/-- The structure-sheaf component of `smallZariskiToZariskiSmall` at `U` is the
`Γ(U, 𝒪_U) ⟶ Γ(X, U.opensRange)` comparison of `IsOpenImmersion.ΓIsoTop`. -/
theorem smallZariskiToZariskiSmall_app (X : Scheme.{u})
    (U : X.smallZariskiSiteᵒᵖ) :
    (smallZariskiToZariskiSmall X).structureSheafMap.hom.app U =
      smallZariskiToZariskiSmallStructureSheafHomApp X U := rfl

/-- The small-Zariski-to-`Zariski.Small` comparison is a ringed equivalence. -/
theorem smallZariskiToZariskiSmall_isRingedEquivalence (X : Scheme.{u}) :
    (smallZariskiToZariskiSmall X).IsRingedEquivalence := by
  letI : ((smallZariskiToZariskiSmall X).sheafPushforwardContinuous
      (A := Type (u + 1))).IsEquivalence := by
    change (Functor.sheafPushforwardContinuous (𝟭 X.smallZariskiSite)
      (Type (u + 1)) X.smallZariskiTopology X.smallZariskiTopology).IsEquivalence
    exact Functor.isEquivalence_of_iso
      (Functor.sheafPushforwardContinuousId _ _).symm
  refine ⟨(smallZariskiToZariskiSmall X).sheafAdjunctionContinuous
    |>.isEquivalence_left_of_isEquivalence_right, ?_⟩
  apply (ObjectProperty.isIso_hom_iff _).mp
  letI : ∀ U, IsIso ((smallZariskiToZariskiSmall X).structureSheafMap.hom.app U) := by
    intro U
    change IsIso ((forget₂ CommRingCat RingCat).map
      (@IsOpenImmersion.ΓIsoTop U.unop.left X U.unop.hom U.unop.prop).hom)
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- Direct image from the transported small Zariski structure sheaf to the canonical
small Zariski structure sheaf, bundled as an exact functor. -/
noncomputable def smallZariskiToZariskiSmallModulePushforward (X : Scheme.{u}) :
    SheafOfModules.{u} (smallZariskiRingSheaf X) ⥤ₑ
      SheafOfModules.{u} (Zariski.Small.structureSheaf X) :=
  ⟨SheafOfModules.pushforward.{u} (F := 𝟭 X.smallZariskiSite)
      (smallZariskiToZariskiSmallStructureSheafHom X),
    by
      exact exact_of_isEquivalence _
        (hF := @RingedSite.Hom.modulePushforward_isEquivalence _ _
          (smallZariskiToZariskiSmall X)
          (smallZariskiToZariskiSmall_isRingedEquivalence X))⟩

/-- The exact derived functor from `D(𝒪_X)` to `D(𝒪_Zar)` obtained by comparing the
opens ringed site, pushing forward along `opensToSmallZariski`, and identifying with
`Zariski.Small.ringedSite` by `smallZariskiToZariskiSmall`. -/
noncomputable def schemeToZariskiDerived (X : Scheme.{u}) :
    RingedSpace.ModuleDerived X.toRingedSpace ⥤
      DerivedCategory (SheafOfModules.{u} (Zariski.Small.structureSheaf X)) :=
  (CategoryTheory.Equivalence.refl : X.toRingedSpace.Modules ≌
      X.toRingedSpace.Modules).mapDerivedCategory.functor ⋙
    (opensToSmallZariskiModulePushforward X).mapDerivedCategory ⋙
      (smallZariskiToZariskiSmallModulePushforward X).mapDerivedCategory

namespace schemeToZariski

/-- The comparison from `D(𝒪_X)` to `D(𝒪_Zar)` preserves quasi-coherent cohomology. -/
theorem mapsTo (X : Scheme.{u}) :
    derivedQuasiCoherentModuleProperty X ≤
      (zariskiSiteProperty X).inverseImage (schemeToZariskiDerived X) :=
  sorry

end schemeToZariski

/-- The restricted comparison `D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Zar)` induced by the ringed-site
identifications of `X` with its small Zariski site. -/
noncomputable def schemeToZariski (X : Scheme.{u}) :
    DerivedQCoh X ⥤ ZariskiSite X :=
  ObjectProperty.FullSubcategory.restrict
    (schemeToZariskiDerived X) (schemeToZariski.mapsTo X)

namespace schemeToZariski

/-- Forgetting quasi-coherence after `schemeToZariski` recovers the ambient derived
comparison. -/
noncomputable def inclusionIso (X : Scheme.{u}) :
    schemeToZariski X ⋙ ZariskiSite.inclusion X ≅
      DerivedQCoh.inclusion X ⋙ schemeToZariskiDerived X :=
  ObjectProperty.FullSubcategory.restrict.compιIso
    (schemeToZariskiDerived X) (mapsTo X)

/-- The underlying derived module of `schemeToZariski` is the ambient derived comparison. -/
@[simp]
theorem obj_obj (X : Scheme.{u}) (E : DerivedQCoh X) :
    ((schemeToZariski X).obj E).obj = (schemeToZariskiDerived X).obj E.obj :=
  rfl

end schemeToZariski

/-- The comparison `D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Zar)` is an equivalence. -/
instance schemeToZariski_isEquivalence (X : Scheme.{u}) :
    (schemeToZariski X).IsEquivalence := sorry

end DerivedQCoh

end AlgebraicGeometry.Scheme
