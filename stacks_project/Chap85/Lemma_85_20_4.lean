/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSite.Hypercovering.CartesianDerivedEquivalence

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

/- Lemma 85.20.4
Derived augmentation pullback is an equivalence from bounded-below modules on
`X.localization U` to bounded-below total-site modules with cartesian cohomology,
with quasi-inverse given by derived augmentation pushforward. -/
@[stacks 0DA7] #check (RingedSite.Hypercovering.modulePlusCartesianEquivalence U K :
  DerivedCategory.Plus (ModuleCat.{w} (X.localization U)) ≌
    RingedSite.Hypercovering.CartesianPlus U K)

#check (RingedSite.Hypercovering.modulePlusCartesianEquivalence_functor U K :
  (RingedSite.Hypercovering.modulePlusCartesianEquivalence U K).functor =
    RingedSite.Hypercovering.plusCartesianFunctor U K)

#check (RingedSite.Hypercovering.modulePlusCartesianEquivalence_inverse U K :
  (RingedSite.Hypercovering.modulePlusCartesianEquivalence U K).inverse =
    RingedSite.Hypercovering.plusCartesianInverse U K)

end RingedSite.Hypercovering
