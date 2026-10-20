/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Cohomology
import ReasLib.CategoryTheory.Sites.Sheafification.FreeAbelian
import StacksCheckRecall

/-! # Remark 85.17.6

Localization at a presheaf identifies hypercoverings and their bounded-below cohomology
comparisons with the corresponding constructions on the localized site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Presheaf CategoryTheory.HypercoveringOf
open CategoryTheory.Sheaf CategoryTheory.Sheaf.CohomologyOverPresheaf
open CategoryTheory.SemiRepresentableFamily

noncomputable section

universe w v u

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) [HasEqualizers C] [HasPullbacks C]
variable (G : Cᵒᵖ ⥤ Type (max w v))

section Sheafification
variable [HasWeakSheafify J (Type (max w v))]

/- Remark 85.17.6 (1): localization at the presheaf presents localization at its sheafification. -/
@[stacks 09X6] #check (CategoryTheory.Presheaf.sheafificationRelocalization_sheafPushforward_isEquivalence J G :
  ((CategoryTheory.Presheaf.sheafificationRelocalization J G).sheafPushforwardContinuous
    (Type (max w v)) (localizationSite J G)
    (localizationSite J ((presheafToSheaf J (Type (max w v))).obj G).obj)).IsEquivalence)

end Sheafification

/- Remark 85.17.6 (2): localization inherits fibre products. -/
@[stacks 09X6] #check (CategoryTheory.Presheaf.hasPullbacks_elementsOp G : HasPullbacks G.Elementsᵒᵖ)

/- Remark 85.17.6 (3): localization inherits equalizers. -/
@[stacks 09X6] #check (CategoryTheory.Presheaf.hasEqualizers_elementsOp G : HasEqualizers G.Elementsᵒᵖ)

/- Remark 85.17.6 (4): hypercoverings of the presheaf correspond to hypercoverings of its
localization site. -/
@[stacks 09X6] #check (CategoryTheory.HypercoveringOf.hypercoveringEquivLocalizedTerminal J G :
  HypercoveringOf J G ≃ HypercoveringOf.Terminal (localizationSite J G))

variable (K : HypercoveringOf J G)
variable [HasSheafify J AddCommGrpCat.{max w v}]
variable [HasWeakSheafify (Presheaf.localizationSite J G) AddCommGrpCat.{max w v}]
variable [HasSheafify (Presheaf.localizationSite J G) AddCommGrpCat.{max w v}]
variable [HasGlobalSectionsFunctor (Presheaf.localizationSite J G) AddCommGrpCat.{max w v}]
variable [∀ P : (G.Elementsᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{max w v},
    (Presheaf.localizationForget G).op.HasPointwiseRightKanExtension P]
variable [HasDerivedCategory.{max u v w} (Sheaf J AddCommGrpCat.{max w v})]
variable [HasDerivedCategory.{max u v w} AddCommGrpCat.{max u v w}]
variable [(homFunctor.{w, v, u} J G).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (Sheaf J AddCommGrpCat.{max w v}))]
variable [(Presheaf.elementsOpInverseImage J G AddCommGrpCat.{max w v} ⋙
      globalSectionsHomFunctor.{max w v} (Presheaf.localizationSite J G)).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (Sheaf J AddCommGrpCat.{max w v}))]
variable [HasDerivedCategory.{max u v w}
    (Sheaf (Presheaf.localizationSite J G) AddCommGrpCat.{max w v})]
variable [(Presheaf.elementsOpInverseImage J G AddCommGrpCat.{max w v}).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (Sheaf J AddCommGrpCat.{max w v}))]
variable [(globalSectionsHomFunctor.{max w v} (Presheaf.localizationSite J G)).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (Presheaf.localizationSite J G) AddCommGrpCat.{max w v}))]
variable [HasWeakSheafify
    (overSiteTotalTopology J K.simplicial)
    AddCommGrpCat.{max w v}]
variable [HasSheafify
    (overSiteTotalTopology J K.simplicial)
    AddCommGrpCat.{max w v}]
variable [HasGlobalSectionsFunctor
    (overSiteTotalTopology J K.simplicial)
    AddCommGrpCat.{max w v}]
variable [∀ P : (Grothendieck (overSiteDiagram K.simplicial))ᵒᵖ ⥤
      AddCommGrpCat.{max w v},
    (augmentationForget J G K).op.HasPointwiseRightKanExtension P]
variable [HasDerivedCategory.{max u v w}
    (Sheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w v})]
variable [(localizedInverseImageExact J G K).obj.toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (Presheaf.localizationSite J G) AddCommGrpCat.{max w v}))]
variable [(globalSectionsHomFunctor.{max w v} (overSiteTotalTopology J K.simplicial)).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w v}))]
variable [((localizedInverseImageExact J G K).obj ⋙
      globalSectionsHomFunctor.{max w v} (overSiteTotalTopology J K.simplicial)).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (Presheaf.localizationSite J G) AddCommGrpCat.{max w v}))]

/- Remark 85.17.6 (5): bounded-below cohomological descent on the localization uses the
canonical augmentation from the original total site. -/
@[stacks 09X6] #check (CategoryTheory.Sheaf.CohomologyOverPresheaf.rGammaLocalizationInverseImageComparison_app_isIso J G K :
  ∀ E : DerivedCategory.Plus (Sheaf (localizationSite J G) AddCommGrpCat.{max w v}),
    IsIso ((rGammaLocalizationInverseImageComparison J G K).app E))

/- Remark 85.17.6 (6): cohomology over the presheaf is the derived free-abelian-sheaf Hom functor. -/
@[stacks 09X6] #check (CategoryTheory.Sheaf.CohomologyOverPresheaf.derivedFunctor.{max u v w, w, v, u} J G :
  DerivedCategory.Plus (Sheaf J AddCommGrpCat.{max w v}) ⥤
    DerivedCategory.Plus AddCommGrpCat.{max u v w})
#check (CategoryTheory.Sheaf.CohomologyOverPresheaf.homFunctor.{w, v, u} J G :
  Sheaf J AddCommGrpCat.{max w v} ⥤ AddCommGrpCat.{max u v w})
#check (CategoryTheory.Sheaf.globalSectionsHomIso.{max w v} (localizationSite J G) :
  (Γ (localizationSite J G) AddCommGrpCat.{max w v}) ⋙
      AddCommGrpCat.uliftFunctor.{max u v w, max w v} ≅
    globalSectionsHomFunctor.{max w v} (localizationSite J G))

section SheafificationComparison
variable [HasWeakSheafify J (Type (max w v))]
variable [J.PreservesSheafification AddCommGrpCat.free.{max w v}]
#check (CategoryTheory.GrothendieckTopology.freeAbelianSheafComparisonIso.{max w v} J G :
  (Sheaf.composeAndSheafify J AddCommGrpCat.free.{max w v}).obj
      ((presheafToSheaf J (Type (max w v))).obj G) ≅
    J.freeAbelianSheaf.{max w v} G)
end SheafificationComparison

set_option maxHeartbeats 800000 in
/- Remark 85.17.6 (7): localization computes cohomology over the presheaf. -/
@[stacks 09X6] #check (CategoryTheory.Sheaf.CohomologyOverPresheaf.rGammaOverPresheafLocalizationComparison_app_isIso J G :
  ∀ E : DerivedCategory.Plus (Sheaf J AddCommGrpCat.{max w v}),
    IsIso ((rGammaOverPresheafLocalizationComparison J G).app E))

/- Remark 85.17.6: composing localization with the canonical augmentation computes cohomology
over the presheaf on the original hypercovering total site. -/
@[stacks 09X6] #check (CategoryTheory.Sheaf.CohomologyOverPresheaf.rGammaOverPresheafTotalComparison_app_isIso J G K :
  ∀ E : DerivedCategory.Plus (Sheaf J AddCommGrpCat.{max w v}),
    IsIso ((rGammaOverPresheafTotalComparison J G K).app E))
