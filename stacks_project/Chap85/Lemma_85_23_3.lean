/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Simplicial.UnboundedDescent

/-!
# Lemma 85.23.3

Let `(C, O_C)` be a ringed site. Assume given weak Serre subcategories `A_U ⊂ Mod(O_U)`
satisfying conditions (1), (2), and (3). Assume `C` has equalizers and fibre products and
let `K` be a hypercovering. Let `((C / K)_total, O)` be as in Remark 85.16.5. Let
`A_total ⊂ Mod(O)` denote the weak Serre subcategory of cartesian `O`-modules `F` whose
restriction `F_n` is in `A_{K_n}` for all `n`. Then the functor `La^*` defines an
equivalence `D_A(O_C) ≌ D_{A_total}(O)` with quasi-inverse `Ra_*`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
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

/- Lemma 85.23.3. For a terminal hypercovering and a local restriction-stable weak Serre
family with fiberwise bounded cohomology, canonical `La^*` is an equivalence. The restricted
canonical adjunction below identifies `Ra_*` as its quasi-inverse. -/
@[stacks 0DC7] #check
  (RingedSite.Localization.AtSimplicialSR.pullbackFunctor_isEquivalence A K :
    (RingedSite.Localization.AtSimplicialSR.pullbackFunctor A K).IsEquivalence)

#check (RingedSite.Localization.AtSimplicialSR.pullbackFunctor A K :
  (DerivedCategory.cohomologyIn A.global).FullSubcategory ⥤
    (DerivedCategory.cohomologyIn (A.total K.simplicial)).FullSubcategory)

#check (RingedSite.Localization.AtSimplicialSR.pushforwardFunctor A K :
  (DerivedCategory.cohomologyIn (A.total K.simplicial)).FullSubcategory ⥤
    (DerivedCategory.cohomologyIn A.global).FullSubcategory)

#check (RingedSite.Localization.AtSimplicialSR.cohomologyInDerivedAdjunction A K :
  RingedSite.Localization.AtSimplicialSR.pullbackFunctor A K ⊣
    RingedSite.Localization.AtSimplicialSR.pushforwardFunctor A K)

#check (RingedSite.Localization.AtSimplicialSR.cohomologyInUnit_app_isIso A K :
  ∀ E : (DerivedCategory.cohomologyIn A.global).FullSubcategory,
    IsIso ((RingedSite.Localization.AtSimplicialSR.cohomologyInDerivedAdjunction A K).unit.app E))

#check (RingedSite.Localization.AtSimplicialSR.cohomologyInCounit_app_isIso A K :
  ∀ G : (DerivedCategory.cohomologyIn (A.total K.simplicial)).FullSubcategory,
    IsIso ((RingedSite.Localization.AtSimplicialSR.cohomologyInDerivedAdjunction A K).counit.app G))

end RingedSite.Localization.AtSimplicialSR

end
