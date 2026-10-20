/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_20_4_Equivalence

/-!
# Lemma 85.20.4

Let `C` be a site with fibre products and `X` an object of `C`. Let `O_C` be a
sheaf of rings. Let `K` be a hypercovering of `X`. If `A` is the weak Serre
subcategory of cartesian `O`-modules on `((C / K)_total, O)`, then `La^*`
defines an equivalence `D⁺(O_X) ≌ D_A⁺(O)` with quasi-inverse `Ra_*`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe ι u v w

namespace RingedSite.Hypercovering

open CategoryTheory.Hypercovering (toSliceTerminal)
open SemiRepresentableFamily
  (OverSite overTopology overSiteDiagram overSiteTotalTopology totalForget overMap)

-- Local instance justification (defeq pin): `Hom.moduleCat_hasDerivedCategory` is reducible to `HasDerivedCategory.standard` and is not global; `Plus.ι` and `La^*`/`Ra_*` must share that same derived-category instance.
attribute [local instance] Hom.moduleCat_hasDerivedCategory

variable {X : RingedSite.{u, v, w}}
variable [HasPullbacks X.carrier]
variable (U : X) (K : CategoryTheory.Hypercovering.{ι} X.siteTopology U)
variable [UnivLE.{max ι u v, w}]
variable [UnivLE.{max u v, w}]
variable [HasSheafify
    (overSiteTotalTopology (X.localization U).siteTopology K.toSimplicialObject) (Type w)]
variable [HasWeakSheafify
    (overSiteTotalTopology (X.localization U).siteTopology K.toSimplicialObject) (Type w)]
variable [∀ n : SimplexCategory,
    HasSheafify
      (overTopology (X.localization U).siteTopology (K.toSimplicialObject.obj (op n)))
      (Type w)]
variable [∀ n : SimplexCategory,
    HasWeakSheafify
      (overTopology (X.localization U).siteTopology (K.toSimplicialObject.obj (op n)))
      (Type w)]
variable [∀ P : (Grothendieck (overSiteDiagram K.toSimplicialObject))ᵒᵖ ⥤ Type w,
    (totalForget K.toSimplicialObject).op.HasPointwiseRightKanExtension P]
variable [∀ n : SimplexCategory,
    ∀ P : (OverSite (K.toSimplicialObject.obj (op n)))ᵒᵖ ⥤ Type w,
      (Grothendieck.ι (overSiteDiagram K.toSimplicialObject) (op n)).op.HasPointwiseRightKanExtension
        P]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ∀ P : (OverSite (K.toSimplicialObject.obj (op n)))ᵒᵖ ⥤ Type w,
      (overMap (K.toSimplicialObject.map φ.op)).op.HasPointwiseRightKanExtension P]
variable [(overSiteTotalTopology (X.localization U).siteTopology
    K.toSimplicialObject).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [(X.localization U).siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n : SimplexCategory,
    (overTopology (X.localization U).siteTopology
      (K.toSimplicialObject.obj (op n))).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [toAmbientRestrictScalarsAdjoint (X.localization U)
    (toSliceTerminal X.siteTopology U K)]
variable [stageInclRestrictScalarsAdjoint (X.localization U)
    (toSliceTerminal X.siteTopology U K)]
variable [stageMapRestrictScalarsAdjoint (X.localization U)
    (toSliceTerminal X.siteTopology U K)]
variable [ToposHom.HasModulePullbackDerived
    (Localization.AtSimplicialSR.toAmbient.{ι, max u v, v, w}
      (toSliceTerminal X.siteTopology U K).simplicial :
      ToposHom _ (X.localization U))]
variable [ToposHom.HasModulePushforwardDerived
    (Localization.AtSimplicialSR.toAmbient.{ι, max u v, v, w}
      (toSliceTerminal X.siteTopology U K).simplicial :
      ToposHom _ (X.localization U))]
variable [ToposHom.HasModuleDerivedAdjunction
    (Localization.AtSimplicialSR.toAmbient.{ι, max u v, v, w}
      (toSliceTerminal X.siteTopology U K).simplicial :
      ToposHom _ (X.localization U))]

/-- Lemma 85.20.4
Let `C` be a site with fibre products and `X` an object of `C`. Let `O_C` be a sheaf of
rings. Let `K` be a hypercovering of `X`. Let `A ⊂ Mod(O)` denote the weak Serre subcategory
of cartesian `O`-modules. Then the functor `La^*` defines an equivalence
`D⁺(O_X) ≌ D_A⁺(O)` with quasi-inverse `Ra_*`.

Here `O_X` is the structure sheaf of `X.localization U`, `O` is the structure sheaf of
`site_terminal (X.localization U) (toSliceTerminal X.siteTopology U K)`, `A` is the
object property `cartesianProperty` of cartesian `O`-modules, `La^*` is
`plusCartesianFunctor`, and `Ra_*` is `plusCartesianInverse`. -/
@[stacks 0DA7]
def modulePlusCartesianEquivalence :=
  plusCartesianEquivalence U K

/-- The forward functor of `modulePlusCartesianEquivalence` is `La^*` corestricted to
`D_A⁺(O)`. -/
theorem modulePlusCartesianEquivalence_functor :
    (modulePlusCartesianEquivalence U K).functor = plusCartesianFunctor U K :=
  sorry

/-- The inverse functor of `modulePlusCartesianEquivalence` is `Ra_*` restricted from
`D_A⁺(O)`. -/
theorem modulePlusCartesianEquivalence_inverse :
    (modulePlusCartesianEquivalence U K).inverse = plusCartesianInverse U K :=
  sorry

end RingedSite.Hypercovering
