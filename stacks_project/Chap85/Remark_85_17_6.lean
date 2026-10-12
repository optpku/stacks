/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap85.Remark_85_17_6_Comparison
import ReasLib.CategoryTheory.Sites.Sheafification.FreeAbelian
import StacksCheckRecall

/-!
# Remark 85.17.6

Localization of a site at a set-valued presheaf converts hypercoverings of the presheaf into
site-level hypercoverings, so the cohomological-descent identifications of the section apply
after replacing `C` by `C / G`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Presheaf
open CategoryTheory.HypercoveringOf
open CategoryTheory.Sheaf.CohomologyOverPresheaf
open CategoryTheory.SemiRepresentableFamily
open scoped SemiRepresentableFamily

noncomputable section

universe w v u

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [HasEqualizers C] [HasPullbacks C]
variable (G : Cᵒᵖ ⥤ Type (max w v))

/- Remark 85.17.6 (1): the localization `C / G` is the opposite category of elements of `G`,
and `Sh(C / G)` identifies with the localization of `Sh(C)` at `G#`. -/
@[stacks 09X6] #check @sheafificationRelocalization_sheafPushforward_isEquivalence

/- Remark 85.17.6 (2): if `C` has fibre products, then so does `C / G`. -/
@[stacks 09X6] #check @hasPullbacks_elementsOp

/- Remark 85.17.6 (3): if `C` has equalizers, then so does `C / G`. -/
@[stacks 09X6] #check @hasEqualizers_elementsOp

/- Remark 85.17.6 (4): a hypercovering of `G` is the same thing as a hypercovering of the
site `C / G`. -/
@[stacks 09X6] #check @hypercoveringEquivLocalizedTerminal

variable [HasSheafify J AddCommGrpCat.{max w v}]
variable [HasWeakSheafify (localizationSite J G) AddCommGrpCat.{max w v}]
variable [HasSheafify (localizationSite J G) AddCommGrpCat.{max w v}]
variable [HasGlobalSectionsFunctor (localizationSite J G) AddCommGrpCat.{max w v}]
variable [∀ P : (G.Elementsᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{max w v},
    (localizationForget G).op.HasPointwiseRightKanExtension P]
variable [HasDerivedCategory.{max u v w} (Sheaf J AddCommGrpCat.{max w v})]
variable [HasDerivedCategory.{max u v w} AddCommGrpCat.{max u v w}]
variable [HasDerivedCategory.{max u v w}
    (Sheaf (localizationSite J G) AddCommGrpCat.{max w v})]
variable [(homFunctor J G).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (Sheaf J AddCommGrpCat.{max w v}))]
variable [(elementsOpInverseImage J G AddCommGrpCat.{max w v} ⋙
      localizationHomFunctor J G).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (Sheaf J AddCommGrpCat.{max w v}))]
variable [(localizationHomFunctor J G).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (localizationSite J G) AddCommGrpCat.{max w v}))]

variable (K : HypercoveringOf J G)
variable [HasWeakSheafify
    (overSiteTotalTopology (localizationSite J G) (toLocalizedSimplicial J K))
    AddCommGrpCat.{max w v}]
variable [HasSheafify
    (overSiteTotalTopology (localizationSite J G) (toLocalizedSimplicial J K))
    AddCommGrpCat.{max w v}]
variable [HasGlobalSectionsFunctor
    (overSiteTotalTopology (localizationSite J G) (toLocalizedSimplicial J K))
    AddCommGrpCat.{max w v}]
variable [∀ P : (Grothendieck (overSiteDiagram (toLocalizedSimplicial J K)))ᵒᵖ ⥤
      AddCommGrpCat.{max w v},
    (augmentationForget J G K).op.HasPointwiseRightKanExtension P]
variable [(localizedInverseImage J G K ⋙ totalHomFunctor J G K).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (localizationSite J G) AddCommGrpCat.{max w v}))]
variable [(elementsOpInverseImage J G AddCommGrpCat.{max w v} ⋙
      localizedInverseImage J G K ⋙ totalHomFunctor J G K).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (Sheaf J AddCommGrpCat.{max w v}))]

/-- Remark 85.17.6 (5): for a hypercovering `K` of `G` and `E` in `D⁺(C / G)`, the comparison
`RΓ(C / G, E) ⟶ RΓ((C / K)_total, a⁻¹ E)` is an isomorphism. -/
@[stacks 09X6]
theorem rGammaLocalizationInverseImageComparison_app_isIso
    (E : DerivedCategory.Plus
      (Sheaf (localizationSite J G) AddCommGrpCat.{max w v})) :
    IsIso ((rGammaLocalizationInverseImageComparison J G K).app E) :=
  sorry

/- Remark 85.17.6 (6): `RΓ(G, -)` is the derived functor of `H⁰(G, -) = H⁰(G#, -)`. -/
@[stacks 09X6] #check @derivedFunctor
#check @homFunctor
#check @GrothendieckTopology.freeAbelianSheafComparisonIso

/-- Remark 85.17.6 (7): `RΓ(G, E) ⟶ RΓ(C / G, j⁻¹ E)` is an isomorphism. -/
@[stacks 09X6]
theorem rGammaOverPresheafLocalizationComparison_app_isIso
    (E : DerivedCategory.Plus (Sheaf J AddCommGrpCat.{max w v})) :
    IsIso ((rGammaOverPresheafLocalizationComparison J G).app E) :=
  sorry

/-- Remark 85.17.6 (8): putting the identifications together,
`RΓ(G, E) ⟶ RΓ((C / K)_total, g⁻¹ E)` is an isomorphism for `E` in `D⁺(C)`. -/
@[stacks 09X6]
theorem rGammaOverPresheafTotalComparison_app_isIso
    (E : DerivedCategory.Plus (Sheaf J AddCommGrpCat.{max w v})) :
    IsIso ((rGammaOverPresheafTotalComparison J G K).app E) :=
  sorry
