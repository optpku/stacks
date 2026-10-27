/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ringed
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.UniverseLift
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Universe
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Homology

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u uC vC w z

namespace SheafOfModules

/-- The adequate-module property used degreewise in `DerivedAdeq S τ`. -/
abbrev adequateProperty (S : Scheme.{u}) (τ : StandardTopology) :
    ObjectProperty
      (RingedSite.ModuleCat.{u + 1} (StandardTopology.Big.ringedSite τ S)) :=
  @IsAdequateWith S τ ModuleValuedFunctor.tensorExtensionUnderlyingLifted
    (@affineEvaluationUnderlyingLifted S τ)

set_option backward.isDefEq.respectTransparency false in
/-- Adequacy is invariant under isomorphisms of module sheaves. -/
theorem adequateProperty_of_iso (S : Scheme.{u}) (τ : StandardTopology)
    {F G : RingedSite.ModuleCat.{u + 1} (StandardTopology.Big.ringedSite τ S)}
    (e : F ≅ G) (hF : adequateProperty S τ F) : adequateProperty S τ G := by
  rcases hF with ⟨ι, A, f, hcover, h⟩
  refine ⟨ι, A, f, hcover, fun i ↦ ?_⟩
  rcases h i with ⟨M, N, g, ⟨a⟩⟩
  let e' := (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).mapIso e
  let evalIso : affineEvaluationUnderlyingLifted F (A i) (f i) ≅
      affineEvaluationUnderlyingLifted G (A i) (f i) :=
    NatIso.ofComponents
      (fun B ↦ ((CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj
        (Opposite.op (affineObject (f i) B))).mapIso e')
      (fun g ↦ e'.hom.naturality (affineObjectMap (f i) g).op)
  exact ⟨M, N, g, ⟨evalIso.symm ≪≫ a⟩⟩

/-- The degreewise adequate object property on the unbounded derived module category. -/
abbrev derivedAdequateProperty (S : Scheme.{u}) (τ : StandardTopology) :
    ObjectProperty
      (RingedSite.Hom.ModuleDerived.{u + 1}
        (StandardTopology.Big.ringedSite τ S)) :=
  @DerivedCategory.cohomologyIn _ _ _
    (RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1}
      (StandardTopology.Big.ringedSite τ S))
    (adequateProperty S τ)

/-- The unbounded derived category of modules on the big `τ`-site of `S` whose
cohomology modules are adequate. -/
abbrev DerivedAdeq (S : Scheme.{u}) (τ : StandardTopology) :=
  (derivedAdequateProperty S τ).FullSubcategory

namespace DerivedAdeq

/-- Every homology module of an object of `DerivedAdeq S τ` is adequate. -/
theorem homology_isAdequate (S : Scheme.{u}) (τ : StandardTopology)
    (K : DerivedAdeq S τ) (n : ℤ) :
    IsAdequateWith ModuleValuedFunctor.tensorExtensionUnderlyingLifted
      affineEvaluationUnderlyingLifted
      ((@DerivedCategory.homologyFunctor
        (RingedSite.ModuleCat.{u + 1} (StandardTopology.Big.ringedSite τ S)) _ _
        (RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1}
          (StandardTopology.Big.ringedSite τ S)) n).obj K.obj) :=
  K.property n

end DerivedAdeq

end SheafOfModules

namespace AlgebraicGeometry.StandardTopology.Big

/-- The identity-on-objects morphism from the big fppf ringed site to the big `τ`-ringed site. -/
noncomputable def toFppfHom (τ : StandardTopology) (S : Scheme.{u}) :
    RingedSite.Hom (ringedSite .fppf S) (ringedSite τ S) :=
  Scheme.Site.ringedHom (τ.overTopology S) (StandardTopology.fppf.overTopology S)
    (Over.forget S) (Over.forget S) (𝟭 (Over S)) (𝟙 (Over.forget S))
    (structurePresheaf_isSheaf τ S) (structurePresheaf_isSheaf .fppf S)

/-- The base functor of `toFppfHom τ S` is the identity of `Over S`. -/
theorem toFppfHom_base (τ : StandardTopology) (S : Scheme.{u}) :
    (toFppfHom τ S).base = 𝟭 (Over S) := rfl

/-- The topology-change structure map is the identity on the global-sections presheaf. -/
theorem toFppfHom_structureSheafMap_hom (τ : StandardTopology) (S : Scheme.{u}) :
    (toFppfHom τ S).structureSheafMap.hom =
      𝟙 (Scheme.Site.structurePresheaf (Over.forget S)) := by
  apply NatTrans.ext
  funext U
  change RingCat.ofHom (Scheme.Hom.appTop (𝟙 U.unop.left)).hom = 𝟙 _
  rw [Scheme.Hom.id_appTop]
  rfl

/-- The presheaf direct image is the identity and hence has a left adjoint. -/
theorem toFppfHom_presheafPushforwardIsRightAdjoint
    (τ : StandardTopology) (S : Scheme.{u}) :
    (PresheafOfModules.pushforward.{u + 1}
      (toFppfHom τ S).structureSheafMap.hom).IsRightAdjoint := by
  change (PresheafOfModules.pushforward.{u + 1} (F := 𝟭 (Over S))
    (Scheme.Site.structurePresheafMap (Over.forget S) (Over.forget S)
      (𝟭 (Over S)) (𝟙 (Over.forget S)))).IsRightAdjoint
  rw [show Scheme.Site.structurePresheafMap (Over.forget S) (Over.forget S)
      (𝟭 (Over S)) (𝟙 (Over.forget S)) =
      𝟙 (Scheme.Site.structurePresheaf (Over.forget S)) from
    toFppfHom_structureSheafMap_hom τ S]
  exact (Adjunction.id.ofNatIsoRight
    (PresheafOfModules.pushforwardId.{u + 1}
      (Scheme.Site.structurePresheaf (Over.forget S))).symm).isRightAdjoint

/-- Module direct image along `toFppfHom τ S` has its canonical inverse-image left adjoint. -/
noncomputable def toFppfHom_modulePushforwardIsRightAdjoint
    (τ : StandardTopology) (S : Scheme.{u}) :
    ((toFppfHom τ S).modulePushforward.{u + 1}).IsRightAdjoint := by
  letI := (toFppfHom τ S).base_isContinuous
  letI : (PresheafOfModules.pushforward.{u + 1}
      (toFppfHom τ S).structureSheafMap.hom).IsRightAdjoint :=
    toFppfHom_presheafPushforwardIsRightAdjoint τ S
  letI : HasWeakSheafify (StandardTopology.fppf.overTopology S)
      AddCommGrpCat.{u + 1} :=
    (inferInstance : HasSheafify (StandardTopology.fppf.overTopology S)
      AddCommGrpCat.{u + 1}).isRightAdjoint
  exact (SheafOfModules.PullbackConstruction.adjunction
    (toFppfHom τ S).structureSheafMap).isRightAdjoint

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- On a fixed category and ring presheaf, topology-change inverse image is exact. -/
theorem topologyChange_modulePullback_exact
    {C : Type uC} [Category.{vC} C]
    (J K : GrothendieckTopology C) (R : Cᵒᵖ ⥤ RingCat.{w})
    (hJ : Presheaf.IsSheaf J R) (hK : Presheaf.IsSheaf K R)
    [(𝟭 C).IsContinuous J K]
    [HasSheafify K AddCommGrpCat.{z}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{z}]
    (α : (⟨R, hJ⟩ : Sheaf J RingCat.{w}) ⟶
      ((𝟭 C).sheafPushforwardContinuous RingCat.{w} J K).obj ⟨R, hK⟩)
    (hα : α.hom = 𝟙 R)
    [(PresheafOfModules.pushforward.{z} α.hom).IsRightAdjoint]
    [(SheafOfModules.pushforward.{z} α).IsRightAdjoint] :
    exactFunctor _ _ (SheafOfModules.pullback.{z} α) := by
  letI : CategoryTheory.Limits.PreservesFiniteLimits
      (𝟭 (PresheafOfModules.{z} R)) := by
    letI : CategoryTheory.Limits.PreservesLimitsOfSize.{0, 0}
        (𝟭 (PresheafOfModules.{z} R)) :=
      CategoryTheory.Limits.id_preservesLimitsOfSize
    exact CategoryTheory.Limits.PreservesLimitsOfSize0.preservesFiniteLimits _
  letI : Presheaf.IsLocallyInjective K (𝟙 R) :=
    Presheaf.isLocallyInjective_of_injective K (𝟙 R) (fun _ ↦ Function.injective_id)
  letI : Presheaf.IsLocallySurjective K (𝟙 R) :=
    Presheaf.isLocallySurjective_of_surjective K (𝟙 R) (fun _ ↦ Function.surjective_id)
  letI : CategoryTheory.Limits.PreservesFiniteLimits
      (SheafOfModules.forget.{z} (⟨R, hJ⟩ : Sheaf J RingCat.{w})) :=
    SheafOfModules.Finite.forgetPreservesFiniteLimits _
  let e : PresheafOfModules.pushforward.{z} α.hom ≅
      𝟭 (PresheafOfModules.{z} R) := by
    rw [hα]
    exact PresheafOfModules.pushforwardId R
  letI : CategoryTheory.Limits.PreservesFiniteLimits
      (PresheafOfModules.pullback.{z} α.hom) :=
    CategoryTheory.Limits.preservesFiniteLimits_of_natIso
      ((PresheafOfModules.pullbackPushforwardAdjunction α.hom).leftAdjointIdIso e).symm
  letI : CategoryTheory.Limits.PreservesFiniteLimits
      (PresheafOfModules.pullback.{z} α.hom ⋙
        PresheafOfModules.sheafification.{z}
          (R := (⟨R, hK⟩ : Sheaf K RingCat.{w})) (𝟙 R)) :=
    CategoryTheory.Limits.comp_preservesFiniteLimits _ _
  constructor
  · letI : CategoryTheory.Limits.PreservesFiniteLimits
        (SheafOfModules.forget.{z} (⟨R, hJ⟩ : Sheaf J RingCat.{w}) ⋙
          PresheafOfModules.pullback.{z} α.hom ⋙
            PresheafOfModules.sheafification.{z}
              (R := (⟨R, hK⟩ : Sheaf K RingCat.{w})) (𝟙 R)) :=
      CategoryTheory.Limits.comp_preservesFiniteLimits _ _
    exact CategoryTheory.Limits.preservesFiniteLimits_of_natIso
      (SheafOfModules.pullbackIso α).symm
  · change CategoryTheory.Limits.PreservesFiniteColimits (SheafOfModules.pullback α)
    infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Topology-change pullback is exact, since it is module sheafification. -/
theorem toFppfHom_pullback_exact (τ : StandardTopology) (S : Scheme.{u}) :
    exactFunctor _ _
      (@RingedSite.Hom.modulePullback.{u + 1} _ _ (toFppfHom τ S)
        (toFppfHom_modulePushforwardIsRightAdjoint τ S)) := by
  letI := toFppfHom_modulePushforwardIsRightAdjoint τ S
  letI : (PresheafOfModules.pushforward.{u + 1}
      (toFppfHom τ S).structureSheafMap.hom).IsRightAdjoint :=
    toFppfHom_presheafPushforwardIsRightAdjoint τ S
  exact topologyChange_modulePullback_exact.{u + 1, u, u, u + 1}
    (τ.overTopology S) (StandardTopology.fppf.overTopology S)
    (Scheme.Site.structurePresheaf (Over.forget S))
    (structurePresheaf_isSheaf τ S) (structurePresheaf_isSheaf .fppf S)
    (toFppfHom τ S).structureSheafMap (toFppfHom_structureSheafMap_hom τ S)

/-- Module inverse image along `toFppfHom τ S` admits its canonical unbounded left-derived
functor. -/
noncomputable def toFppfHom_modulePullbackHasLeftDerived
    (τ : StandardTopology) (S : Scheme.{u}) :
    Functor.HasLeftDerivedFunctor
      (@RingedSite.Hom.modulePullbackToDerived.{u + 1} _ _ (toFppfHom τ S) inferInstance
        (toFppfHom_modulePushforwardIsRightAdjoint τ S))
      (RingedSite.Hom.ModuleQis.{u + 1} (ringedSite τ S)) := by
  letI := toFppfHom_modulePushforwardIsRightAdjoint τ S
  let F := (toFppfHom τ S).modulePullback.{u + 1}
  letI : CategoryTheory.Limits.PreservesFiniteLimits F :=
    (toFppfHom_pullback_exact τ S).1
  letI : CategoryTheory.Limits.PreservesFiniteColimits F :=
    (toFppfHom_pullback_exact τ S).2
  letI : F.Additive :=
    CategoryTheory.leftExactFunctor_le_additiveFunctor _ _ F
      (toFppfHom_pullback_exact τ S).1
  letI := RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1} (ringedSite τ S)
  letI := RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1} (ringedSite .fppf S)
  letI : F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactorsh.hom
      (RingedSite.Hom.ModuleQis.{u + 1} (ringedSite τ S)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ F.mapDerivedCategoryFactorsh
  exact Functor.HasLeftDerivedFunctor.mk' (LF := F.mapDerivedCategory)
    (α := F.mapDerivedCategoryFactorsh.hom)

/-- The topology-change morphism `toFppfHom τ S` is flat on module sheaves. -/
noncomputable def toFppfHom_isFlat (τ : StandardTopology) (S : Scheme.{u}) :
    @RingedSite.Hom.IsFlat.{u + 1, u + 1, u, u + 1, u, u} _ _
      (toFppfHom τ S) (toFppfHom_modulePushforwardIsRightAdjoint τ S) := by
  letI := toFppfHom_modulePushforwardIsRightAdjoint τ S
  exact ⟨toFppfHom_pullback_exact τ S⟩

end AlgebraicGeometry.StandardTopology.Big

namespace SheafOfModules.DerivedAdeq

/-- Pullback from the big `τ`-site to the big fppf site preserves adequacy. -/
theorem toFppf_mapsAdequate (S : Scheme.{u}) (τ : StandardTopology) :
      SheafOfModules.adequateProperty S τ ≤
      (SheafOfModules.adequateProperty S .fppf).inverseImage
        (@RingedSite.Hom.modulePullback.{u + 1} _ _
          (StandardTopology.Big.toFppfHom τ S)
          (StandardTopology.Big.toFppfHom_modulePushforwardIsRightAdjoint τ S)) := sorry

/-- Pullback from adequate modules on the big `τ`-site to adequate modules on the big fppf
site. -/
noncomputable abbrev toFppfAdeq (S : Scheme.{u}) (τ : StandardTopology) :
    (SheafOfModules.adequateProperty S τ).FullSubcategory ⥤
      (SheafOfModules.adequateProperty S .fppf).FullSubcategory :=
  ObjectProperty.FullSubcategory.restrict
    (@RingedSite.Hom.modulePullback.{u + 1} _ _
      (StandardTopology.Big.toFppfHom τ S)
      (StandardTopology.Big.toFppfHom_modulePushforwardIsRightAdjoint τ S))
    (toFppf_mapsAdequate S τ)

/-- Underived pullback along `toFppfHom τ S`, restricted to adequate modules, is an
equivalence. -/
instance toFppfAdeq_isEquivalence (S : Scheme.{u}) (τ : StandardTopology) :
    Functor.IsEquivalence (toFppfAdeq S τ) := sorry

/-- Derived pullback from the big `τ`-site to the big fppf site preserves degreewise
adequacy. -/
theorem toFppf_mapsDerivedAdequate (S : Scheme.{u}) (τ : StandardTopology) :
    SheafOfModules.derivedAdequateProperty S τ ≤
      (SheafOfModules.derivedAdequateProperty S .fppf).inverseImage
        (@RingedSite.Hom.modulePullbackDerived.{u + 1} _ _
          (StandardTopology.Big.toFppfHom τ S) inferInstance inferInstance
          (StandardTopology.Big.toFppfHom_modulePushforwardIsRightAdjoint τ S)
          (StandardTopology.Big.toFppfHom_modulePullbackHasLeftDerived τ S)) := by
  let f := StandardTopology.Big.toFppfHom τ S
  letI := StandardTopology.Big.toFppfHom_modulePushforwardIsRightAdjoint τ S
  letI := StandardTopology.Big.toFppfHom_modulePullbackHasLeftDerived τ S
  let F := f.modulePullback.{u + 1}
  letI : CategoryTheory.Limits.PreservesFiniteLimits F :=
    (StandardTopology.Big.toFppfHom_pullback_exact τ S).1
  letI : CategoryTheory.Limits.PreservesFiniteColimits F :=
    (StandardTopology.Big.toFppfHom_pullback_exact τ S).2
  letI : F.Additive :=
    CategoryTheory.leftExactFunctor_le_additiveFunctor _ _ F
      (StandardTopology.Big.toFppfHom_pullback_exact τ S).1
  letI := RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1}
    (StandardTopology.Big.ringedSite τ S)
  letI := RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1}
    (StandardTopology.Big.ringedSite .fppf S)
  letI : F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactorsh.hom
      (RingedSite.Hom.ModuleQis.{u + 1} (StandardTopology.Big.ringedSite τ S)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ F.mapDerivedCategoryFactorsh
  let e : F.mapDerivedCategory ≅ f.modulePullbackDerived.{u + 1} :=
    Functor.leftDerivedUnique _ _ F.mapDerivedCategoryFactorsh.hom
      ((RingedSite.Hom.modulePullbackToDerived.{u + 1} f).totalLeftDerivedCounit
        (RingedSite.Hom.moduleLocalization.{u + 1} (StandardTopology.Big.ringedSite τ S))
        (RingedSite.Hom.ModuleQis.{u + 1} (StandardTopology.Big.ringedSite τ S)))
      (RingedSite.Hom.ModuleQis.{u + 1} (StandardTopology.Big.ringedSite τ S))
  intro K hK n
  exact SheafOfModules.adequateProperty_of_iso S .fppf
    ((Functor.MapDerivedCategory.homologyIso F K n).symm ≪≫
      (DerivedCategory.homologyFunctor
        (RingedSite.ModuleCat.{u + 1} (StandardTopology.Big.ringedSite .fppf S)) n).mapIso
        (e.app K))
    (toFppf_mapsAdequate S τ _ (hK n))

/-- The canonical derived pullback from adequate-cohomology complexes on the big `τ`-site
to adequate-cohomology complexes on the big fppf site. -/
noncomputable abbrev toFppf (S : Scheme.{u}) (τ : StandardTopology) :
    DerivedAdeq S τ ⥤ DerivedAdeq S .fppf :=
  ObjectProperty.FullSubcategory.restrict
    (@RingedSite.Hom.modulePullbackDerived.{u + 1} _ _
      (StandardTopology.Big.toFppfHom τ S) inferInstance inferInstance
      (StandardTopology.Big.toFppfHom_modulePushforwardIsRightAdjoint τ S)
      (StandardTopology.Big.toFppfHom_modulePullbackHasLeftDerived τ S))
    (toFppf_mapsDerivedAdequate S τ)

/-- `toFppf S τ` is the generic restricted derived pullback along the canonical
identity-on-objects morphism of ringed sites. -/
theorem toFppf_def (S : Scheme.{u}) (τ : StandardTopology) :
    toFppf S τ =
      ObjectProperty.FullSubcategory.restrict
        (@RingedSite.Hom.modulePullbackDerived.{u + 1} _ _
          (StandardTopology.Big.toFppfHom τ S) inferInstance inferInstance
          (StandardTopology.Big.toFppfHom_modulePushforwardIsRightAdjoint τ S)
          (StandardTopology.Big.toFppfHom_modulePullbackHasLeftDerived τ S))
        (toFppf_mapsDerivedAdequate S τ) := rfl

/-- The canonical derived pullback from any standard big site to the big fppf site is an
equivalence on complexes with adequate cohomology. -/
noncomputable instance toFppf_isEquivalence (S : Scheme.{u}) (τ : StandardTopology) :
    Functor.IsEquivalence (toFppf S τ) := sorry

end SheafOfModules.DerivedAdeq

end
