/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_18_4_Equivalence

/-!
# Lemma 85.18.4

Let `C` be a site with equalizers and fibre products, let `O_C` be a sheaf of
rings, and let `K` be a hypercovering. If `A` is the weak Serre subcategory of
cartesian `O`-modules on `((C / K)_total, O)`, then `La^*` defines an
equivalence `D⁺(O_C) ≌ D_A⁺(O)` with quasi-inverse `Ra_*`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe ι u v w

namespace RingedSite.Localization.AtSimplicialSR

open SemiRepresentableFamily
  (OverSite overTopology overSiteDiagram overSiteTotalTopology totalForget overMap)

-- Local instance justification (defeq pin): `Hom.moduleCat_hasDerivedCategory` is reducible to `HasDerivedCategory.standard` and is not global; `Plus.ι` and `modulePullbackDerived`/`modulePushforwardDerived` must share that same derived-category instance.
attribute [local instance] Hom.moduleCat_hasDerivedCategory

variable {X : RingedSite.{u, v, w}}
variable [h_eq : HasEqualizers X.carrier] [h_pb : HasPullbacks X.carrier]
include h_eq h_pb
variable (K : HypercoveringOf.Terminal.{ι} X.siteTopology)
variable [UnivLE.{max ι u v, w}]
variable [UnivLE.{max u v, w}]
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
variable [X.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
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

/-- Lemma 85.18.4
Let `C` be a site with equalizers and fibre products. Let `O_C` be a sheaf of rings. Let `K`
be a hypercovering. Let `A ⊂ Mod(O)` denote the weak Serre subcategory of cartesian `O`-modules.
Then the functor `La^*` defines an equivalence `D⁺(O_C) ≌ D_A⁺(O)` with quasi-inverse `Ra_*`. -/
@[stacks 0DA2]
def modulePlusCartesianEquivalence :
    DerivedCategory.Plus (ModuleCat.{w} X) ≌ CartesianPlus K :=
  plusCartesianEquivalence K

/-- The forward functor of `modulePlusCartesianEquivalence` is `La^*` corestricted to
`D_A⁺(O)`. -/
theorem modulePlusCartesianEquivalence_functor :
    (modulePlusCartesianEquivalence K).functor = plusCartesianFunctor K :=
  sorry

/-- The inverse functor of `modulePlusCartesianEquivalence` is `Ra_*` restricted from
`D_A⁺(O)`. -/
theorem modulePlusCartesianEquivalence_inverse :
    (modulePlusCartesianEquivalence K).inverse = plusCartesianInverse K :=
  sorry

end RingedSite.Localization.AtSimplicialSR
