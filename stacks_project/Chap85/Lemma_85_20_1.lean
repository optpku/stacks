/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSite.Hypercovering.ModuleDescent

/-!
# Lemma 85.20.1

Pullback along a hypercovering of an object is fully faithful, with essential
image the cartesian modules and quasi-inverse the augmentation direct image.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe ι u v w

open CategoryTheory.Hypercovering (toSliceTerminal)
open RingedSite.Hypercovering
open SemiRepresentableFamily
  (OverSite overTopology overSiteDiagram overSiteTotalTopology totalForget overMap)

variable {X : RingedSite.{u, v, w}}
variable [HasPullbacks X.carrier]
variable (U : X) (K : CategoryTheory.Hypercovering.{ι} X.siteTopology U)
variable [UnivLE.{max ι u v, w}]
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

/- Lemma 85.20.1
Pullback identifies modules over the restricted structure sheaf with cartesian
modules on the total site; direct image is the quasi-inverse. -/
@[stacks 0DA4] #check (RingedSite.Hypercovering.moduleCartesianEquivalence U K :
  SheafOfModules.{w} (X.localization U).structureSheaf ≌
    RingedSite.Localization.AtSimplicialSR.Cartesian (X := X.localization U) K.toSimplicialObject)

#check (RingedSite.Hypercovering.moduleCartesianEquivalence_functor U K :
  (RingedSite.Hypercovering.moduleCartesianEquivalence U K).functor =
    RingedSite.Hypercovering.cartesianFunctor_terminal (X.localization U)
      (toSliceTerminal X.siteTopology U K))

#check (RingedSite.Hypercovering.moduleCartesianEquivalence_inverse U K :
  (RingedSite.Hypercovering.moduleCartesianEquivalence U K).inverse =
    RingedSite.Hypercovering.cartesianInverse_terminal (X.localization U)
      (toSliceTerminal X.siteTopology U K))

#check (RingedSite.Hypercovering.module_mem_essImage_iff_isCartesian U K :
  ∀ G : SheafOfModules.{w}
      (RingedSite.Hypercovering.ringSheaf_terminal (X.localization U)
        (toSliceTerminal X.siteTopology U K)),
    (RingedSite.Hypercovering.modulePullback_terminal (X.localization U)
      (toSliceTerminal X.siteTopology U K)).essImage G ↔
    RingedSite.Hypercovering.IsCartesian_terminal (X.localization U)
      (toSliceTerminal X.siteTopology U K) G)

#check (RingedSite.Hypercovering.modulePullback_fullyFaithful U K :
  (RingedSite.Hypercovering.modulePullback_terminal (X.localization U)
    (toSliceTerminal X.siteTopology U K)).FullyFaithful)
