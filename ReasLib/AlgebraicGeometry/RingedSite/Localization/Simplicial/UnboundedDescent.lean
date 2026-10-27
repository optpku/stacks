/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Adjunction
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Terminal
public import ReasLib.AlgebraicGeometry.RingedSite.FiberwiseSerre.Simplicial
public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Simplicial.ModuleDescent
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Adjunction

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

/-- `La^*` sends derived objects with cohomology in `A` to derived objects with cohomology in
`A_total`. -/
theorem mapsPullbackDerived :
    DerivedCategory.cohomologyIn A.global ≤
      (DerivedCategory.cohomologyIn (A.total K.simplicial)).inverseImage
        (toAmbient K.simplicial).modulePullbackDerived := sorry

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
        (toAmbient K.simplicial).modulePushforwardDerived := sorry

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

/-- The canonical derived pullback--pushforward adjunction restricts to the
cohomology-in full subcategories. -/
def cohomologyInDerivedAdjunction : pullbackFunctor A K ⊣ pushforwardFunctor A K :=
  FullSubcategory.adjunction (toAmbient K.simplicial).modulePullbackDerived
    (toAmbient K.simplicial).modulePushforwardDerived
    (ToposHom.moduleDerivedAdjunction (toAmbient K.simplicial))
    (mapsPullbackDerived A K) (mapsPushforwardDerived A K)

/-- The unit of the restricted derived adjunction is invertible on every object
with global fiberwise cohomology. -/
theorem cohomologyInUnit_app_isIso
    (E : (DerivedCategory.cohomologyIn A.global).FullSubcategory) :
    IsIso ((cohomologyInDerivedAdjunction A K).unit.app E) := sorry

/-- The counit of the restricted derived adjunction is invertible on every object
with cartesian degreewise fiberwise cohomology. -/
theorem cohomologyInCounit_app_isIso
    (G : (DerivedCategory.cohomologyIn (A.total K.simplicial)).FullSubcategory) :
    IsIso ((cohomologyInDerivedAdjunction A K).counit.app G) := sorry

/-- Derived augmentation pullback on a terminal hypercovering is an equivalence
between the global and cartesian degreewise fiberwise cohomology subcategories. -/
theorem pullbackFunctor_isEquivalence : (pullbackFunctor A K).IsEquivalence := sorry

end RingedSite.Localization.AtSimplicialSR

end
