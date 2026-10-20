/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_23_3_Equivalence
public import stacks_project.Chap85.Lemma_85_23_3_Fiberwise
public import stacks_project.Chap85.Lemma_85_23_3_Total

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

/-- Lemma 85.23.3
Let `(C, O_C)` be a ringed site. Assume given weak Serre subcategories `A_U ⊂ Mod(O_U)`
satisfying conditions (1), (2), and (3). Assume `C` has equalizers and fibre products and let
`K` be a hypercovering. Let `((C / K)_total, O)` be as in Remark 85.16.5. Let `A_total ⊂ Mod(O)`
denote the weak Serre subcategory of cartesian `O`-modules `F` whose restriction `F_n` is in
`A_{K_n}` for all `n`. Then the functor `La^*` defines an equivalence
`D_A(O_C) ≌ D_{A_total}(O)` with quasi-inverse `Ra_*`. -/
@[stacks 0DC7]
def moduleCohomologyInEquivalence :
    (DerivedCategory.cohomologyIn A.global).FullSubcategory ≌
      (DerivedCategory.cohomologyIn (A.total K.simplicial)).FullSubcategory :=
  cohomologyInEquivalence A K

/-- The forward functor of `moduleCohomologyInEquivalence` is `La^*` corestricted to
`D_{A_total}(O)`. -/
theorem moduleCohomologyInEquivalence_functor :
    (moduleCohomologyInEquivalence A K).functor = pullbackFunctor A K :=
  sorry

/-- The inverse functor of `moduleCohomologyInEquivalence` is `Ra_*` restricted from
`D_{A_total}(O)`. -/
theorem moduleCohomologyInEquivalence_inverse :
    (moduleCohomologyInEquivalence A K).inverse = pushforwardFunctor A K :=
  sorry

end RingedSite.Localization.AtSimplicialSR

end
