/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSite.Hypercovering.DerivedGlobalSections
public import stacks_project.Chap85.Lemma_85_20_2_Adjunction

/-!
# Lemma 85.20.3

Let `C` be a site with fibre products and `X` an object of `C`. Let `O_C` be a
sheaf of rings, and let `K` be a hypercovering of `X`. Then there is a canonical
isomorphism `RΓ(X, E) ≅ RΓ((C / K)_total, La^* E)` in `D(Ab)` for every `E` in
`D(O_C)`. Here `RΓ(X, E)` is derived global sections on `C / X` of the
canonical derived restriction of `E`; augmentation pullback is applied to that
restriction as well.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe ι u v w

namespace RingedSite.Hypercovering

open CategoryTheory.Hypercovering (toSliceTerminal)
open SemiRepresentableFamily (overSiteDiagram overSiteTotalTopology totalForget)

variable {X : RingedSite.{u, v, w}}
variable [HasPullbacks X.carrier]
variable (U : X) (K : CategoryTheory.Hypercovering.{ι} X.siteTopology U)
variable [UnivLE.{max ι u v, w}]
variable [UnivLE.{max u v, w}]
variable [HasSheafify
    (overSiteTotalTopology (X.localization U).siteTopology K.toSimplicialObject) (Type w)]
variable [∀ P : (Grothendieck (overSiteDiagram K.toSimplicialObject))ᵒᵖ ⥤ Type w,
    (totalForget K.toSimplicialObject).op.HasPointwiseRightKanExtension P]
variable [(overSiteTotalTopology (X.localization U).siteTopology
    K.toSimplicialObject).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [(X.localization U).siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [HasWeakSheafify (X.localization U).siteTopology AddCommGrpCat.{w}]
variable [HasWeakSheafify
    (site_terminal (X.localization U)
      (toSliceTerminal X.siteTopology U K)).siteTopology AddCommGrpCat.{w}]
variable [HasGlobalSectionsFunctor (X.localization U).siteTopology AddCommGrpCat.{w}]
variable [HasGlobalSectionsFunctor
    (site_terminal (X.localization U)
      (toSliceTerminal X.siteTopology U K)).siteTopology AddCommGrpCat.{w}]
variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{w} (X.localization U))]
variable [IsGrothendieckAbelian
    (RingedSite.ModuleCat.{w}
      (site_terminal (X.localization U) (toSliceTerminal X.siteTopology U K)))]

/- Lemma 85.20.3: The canonical derived global-sections comparison is invertible
for every ambient derived module, restricted to the localized ringed site. -/
@[stacks 0DA6] #check
  (RingedSite.Hypercovering.rGammaPullbackComparison_restrict_app_isIso U K :
    ∀ E : Hom.ModuleDerived.{w} X,
      IsIso ((RingedSite.Hypercovering.rGammaPullbackComparison U K).app
        ((RingedSite.Hom.localizedRestrictionDerived.{w} X U).obj E)))

-- The slice comparison is also an isomorphism of functors.
#check
  (RingedSite.Localization.AtSimplicialSR.rGammaPullbackComparison_isIso
    (X := X.localization U) (toSliceTerminal X.siteTopology U K) :
    IsIso (RingedSite.Hypercovering.rGammaPullbackComparison U K))

end RingedSite.Hypercovering
