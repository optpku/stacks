/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Adjunction
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Terminal
public import stacks_project.Chap85.Lemma_85_18_1_Equivalence
public import stacks_project.Chap85.Lemma_85_23_3_Total

/-!
# Unbounded hypercovering equivalence on cohomology-in subcategories

If `K` is a hypercovering of the terminal presheaf and `A_U` is a fiberwise weak Serre family,
the derived inverse image `La^*` implements an equivalence
`D_A(O_C) ≌ D_{A_total}(O)` with quasi-inverse `Ra_*`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ObjectProperty
open RingedSite
open RingedSite.FiberwiseSerre
open RingedSite.Hom
open RingedSite.Localization
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe ι wι u v w

namespace RingedSite.Localization.AtSimplicialSR

open SemiRepresentableFamily
  (OverSite overTopology overSiteDiagram overSiteTotalTopology totalForget overMap)

-- Local instance justification (defeq pin): `Hom.moduleCat_hasDerivedCategory` is reducible to `HasDerivedCategory.standard` and is not global; cohomologyIn FullSubcategory and `toAmbient.modulePullbackDerived`/`modulePushforwardDerived` must share that same derived-category instance.
attribute [local instance] Hom.moduleCat_hasDerivedCategory

variable {X : RingedSite.{u, v, w}}
variable [h_eq : HasEqualizers X.carrier] [h_pb : HasPullbacks X.carrier]
include h_eq h_pb
variable [UnivLE.{max u v, w}]
variable [X.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ U : X, (X.siteTopology.over U).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ {U V : X} (f : V ⟶ U),
    (SheafOfModules.restrictScalars.{w} (relocalization X f).structureMap).IsRightAdjoint]
variable (A : FiberwiseSerre.{wι, u, v, w} X)
variable (K : HypercoveringOf.Terminal.{ι} X.siteTopology)
variable [UnivLE.{max ι u v, w}]
variable [HasSheafify (overSiteTotalTopology X.siteTopology K.simplicial) (Type w)]
variable [HasWeakSheafify (overSiteTotalTopology X.siteTopology K.simplicial) (Type w)]
variable [∀ n : SimplexCategory,
    HasSheafify (overTopology X.siteTopology (K.simplicial.obj (op n))) (Type w)]
variable [∀ n : SimplexCategory,
    HasWeakSheafify (overTopology X.siteTopology (K.simplicial.obj (op n))) (Type w)]
variable [∀ P : (Grothendieck (overSiteDiagram K.simplicial))ᵒᵖ ⥤ Type w,
    (totalForget K.simplicial).op.HasPointwiseRightKanExtension P]
variable [∀ n : SimplexCategory, ∀ P : (OverSite (K.simplicial.obj (op n)))ᵒᵖ ⥤ Type w,
    (Grothendieck.ι (overSiteDiagram K.simplicial) (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ∀ P : (OverSite (K.simplicial.obj (op n)))ᵒᵖ ⥤ Type w,
      (overMap (K.simplicial.map φ.op)).op.HasPointwiseRightKanExtension P]
variable [(overSiteTotalTopology X.siteTopology K.simplicial).HasSheafCompose
    (CategoryTheory.forget RingCat.{w})]
variable [∀ n : SimplexCategory,
    (overTopology X.siteTopology (K.simplicial.obj (op n))).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
variable [(SheafOfModules.restrictScalars.{w}
    (toAmbient K.simplicial).structureMap).IsRightAdjoint]
variable [∀ n : SimplexCategory,
    (SheafOfModules.restrictScalars.{w}
      (stageIncl K.simplicial n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (stageMap K.simplicial φ).structureMap).IsRightAdjoint]
variable [ToposHom.HasModulePullbackDerived (toAmbient K.simplicial)]
variable [ToposHom.HasModulePushforwardDerived (toAmbient K.simplicial)]
variable [ToposHom.HasModuleDerivedAdjunction (toAmbient K.simplicial)]

/-- The functor `a^*` corestricted to `A ⥤ A_total`. -/
def moduleFiberwiseFunctor :
    A.global.FullSubcategory ⥤ (A.total K.simplicial).FullSubcategory :=
  FullSubcategory.restrict (toAmbient K.simplicial).modulePullback
    (modulePullback_maps_global A K.simplicial)

/-- The functor `a_*` restricted from `A_total` to `A`. -/
def moduleFiberwiseInverse :
    (A.total K.simplicial).FullSubcategory ⥤ A.global.FullSubcategory :=
  FullSubcategory.restrict (toAmbient K.simplicial).modulePushforward
    (modulePushforward_maps_total A K.simplicial)

/-- The unit `F ⟶ a_* a^* F` is an isomorphism on the global subcategory `A`. -/
theorem moduleFiberwiseUnit_app_isIso (F : A.global.FullSubcategory) :
    IsIso ((toAmbient K.simplicial).moduleAdjunction.unit.app F.obj) :=
  sorry

/-- The unit isomorphism `𝟭 ≅ a^* ⋙ a_*` on `A`. -/
def moduleFiberwiseUnitIso :
    𝟭 A.global.FullSubcategory ≅
      moduleFiberwiseFunctor A K ⋙ moduleFiberwiseInverse A K :=
  NatIso.ofComponents
    (fun F ↦
      A.global.isoMk
        (@asIso _ _ _ _
          ((toAmbient K.simplicial).moduleAdjunction.unit.app F.obj)
          (moduleFiberwiseUnit_app_isIso A K F)))
    sorry

/-- The counit `a^* a_* G ⟶ G` is an isomorphism on `A_total`. -/
theorem moduleFiberwiseCounit_app_isIso
    (G : (A.total K.simplicial).FullSubcategory) :
    IsIso ((toAmbient K.simplicial).moduleAdjunction.counit.app G.obj) :=
  sorry

/-- The counit isomorphism `a_* ⋙ a^* ≅ 𝟭` on `A_total`. -/
def moduleFiberwiseCounitIso :
    moduleFiberwiseInverse A K ⋙ moduleFiberwiseFunctor A K ≅
      𝟭 (A.total K.simplicial).FullSubcategory :=
  NatIso.ofComponents
    (fun G ↦
      (A.total K.simplicial).isoMk
        (@asIso _ _ _ _
          ((toAmbient K.simplicial).moduleAdjunction.counit.app G.obj)
          (moduleFiberwiseCounit_app_isIso A K G)))
    sorry

/-- On modules, `a^* : A ≌ A_total` with quasi-inverse `a_*`. -/
def moduleFiberwiseEquivalence :
    A.global.FullSubcategory ≌ (A.total K.simplicial).FullSubcategory :=
  CategoryTheory.Equivalence.mk (moduleFiberwiseFunctor A K) (moduleFiberwiseInverse A K)
    (moduleFiberwiseUnitIso A K) (moduleFiberwiseCounitIso A K)

/-- `La^*` sends derived objects with cohomology in `A` to derived objects with cohomology in
`A_total`. -/
theorem mapsPullbackDerived :
    DerivedCategory.cohomologyIn A.global ≤
      (DerivedCategory.cohomologyIn (A.total K.simplicial)).inverseImage
        (toAmbient K.simplicial).modulePullbackDerived :=
  sorry

/-- The functor `La^*` corestricted to `D_A(O_C) ⥤ D_{A_total}(O)`. -/
def pullbackFunctor :
    (DerivedCategory.cohomologyIn A.global).FullSubcategory ⥤
      (DerivedCategory.cohomologyIn (A.total K.simplicial)).FullSubcategory :=
  FullSubcategory.restrict (toAmbient K.simplicial).modulePullbackDerived
    (mapsPullbackDerived A K)

/-- Forgetting `D_{A_total}(O)` recovers `La^*` after the cohomology-in inclusion. -/
def pullbackFunctor_comp_ι :
    pullbackFunctor A K ⋙ (DerivedCategory.cohomologyIn (A.total K.simplicial)).ι ≅
      (DerivedCategory.cohomologyIn A.global).ι ⋙
        (toAmbient K.simplicial).modulePullbackDerived :=
  FullSubcategory.restrict.compιIso (toAmbient K.simplicial).modulePullbackDerived
    (mapsPullbackDerived A K)

/-- `Ra_*` sends derived objects with cohomology in `A_total` to derived objects with
cohomology in `A`. -/
theorem mapsPushforwardDerived :
    DerivedCategory.cohomologyIn (A.total K.simplicial) ≤
      (DerivedCategory.cohomologyIn A.global).inverseImage
        (toAmbient K.simplicial).modulePushforwardDerived :=
  sorry

/-- The functor `Ra_*` restricted from `D_{A_total}(O)` to `D_A(O_C)`. -/
def pushforwardFunctor :
    (DerivedCategory.cohomologyIn (A.total K.simplicial)).FullSubcategory ⥤
      (DerivedCategory.cohomologyIn A.global).FullSubcategory :=
  FullSubcategory.restrict (toAmbient K.simplicial).modulePushforwardDerived
    (mapsPushforwardDerived A K)

/-- Forgetting `D_A(O_C)` recovers `Ra_*` after the cohomology-in inclusion. -/
def pushforwardFunctor_comp_ι :
    pushforwardFunctor A K ⋙ (DerivedCategory.cohomologyIn A.global).ι ≅
      (DerivedCategory.cohomologyIn (A.total K.simplicial)).ι ⋙
        (toAmbient K.simplicial).modulePushforwardDerived :=
  FullSubcategory.restrict.compιIso (toAmbient K.simplicial).modulePushforwardDerived
    (mapsPushforwardDerived A K)

/-- The derived unit `E ⟶ Ra_* La^* E` is an isomorphism on `D_A(O_C)`. -/
theorem cohomologyInUnit_app_isIso
    (E : (DerivedCategory.cohomologyIn A.global).FullSubcategory) :
    IsIso ((ToposHom.moduleDerivedAdjunction (toAmbient K.simplicial)).unit.app E.obj) :=
  sorry

/-- The unit isomorphism `𝟭 ≅ La^* ⋙ Ra_*` on `D_A(O_C)`. -/
def cohomologyInUnitIso :
    𝟭 (DerivedCategory.cohomologyIn A.global).FullSubcategory ≅
      pullbackFunctor A K ⋙ pushforwardFunctor A K :=
  NatIso.ofComponents
    (fun E ↦
      (DerivedCategory.cohomologyIn A.global).isoMk
        (@asIso _ _ _ _
          ((ToposHom.moduleDerivedAdjunction (toAmbient K.simplicial)).unit.app E.obj)
          (cohomologyInUnit_app_isIso A K E)))
    sorry

/-- The derived counit `La^* Ra_* G ⟶ G` is an isomorphism on `D_{A_total}(O)`. -/
theorem cohomologyInCounit_app_isIso
    (G : (DerivedCategory.cohomologyIn (A.total K.simplicial)).FullSubcategory) :
    IsIso ((ToposHom.moduleDerivedAdjunction (toAmbient K.simplicial)).counit.app G.obj) :=
  sorry

/-- The counit isomorphism `Ra_* ⋙ La^* ≅ 𝟭` on `D_{A_total}(O)`. -/
def cohomologyInCounitIso :
    pushforwardFunctor A K ⋙ pullbackFunctor A K ≅
      𝟭 (DerivedCategory.cohomologyIn (A.total K.simplicial)).FullSubcategory :=
  NatIso.ofComponents
    (fun G ↦
      (DerivedCategory.cohomologyIn (A.total K.simplicial)).isoMk
        (@asIso _ _ _ _
          ((ToposHom.moduleDerivedAdjunction (toAmbient K.simplicial)).counit.app G.obj)
          (cohomologyInCounit_app_isIso A K G)))
    sorry

/-- `La^*` implements an equivalence `D_A(O_C) ≌ D_{A_total}(O)` with quasi-inverse `Ra_*`. -/
def cohomologyInEquivalence :
    (DerivedCategory.cohomologyIn A.global).FullSubcategory ≌
      (DerivedCategory.cohomologyIn (A.total K.simplicial)).FullSubcategory :=
  CategoryTheory.Equivalence.mk (pullbackFunctor A K) (pushforwardFunctor A K)
    (cohomologyInUnitIso A K) (cohomologyInCounitIso A K)

/-- The forward functor of `cohomologyInEquivalence` is `La^*` corestricted to `D_{A_total}`. -/
theorem cohomologyInEquivalence_functor :
    (cohomologyInEquivalence A K).functor = pullbackFunctor A K :=
  sorry

/-- The inverse functor of `cohomologyInEquivalence` is `Ra_*` restricted from `D_{A_total}`. -/
theorem cohomologyInEquivalence_inverse :
    (cohomologyInEquivalence A K).inverse = pushforwardFunctor A K :=
  sorry

end RingedSite.Localization.AtSimplicialSR

end
