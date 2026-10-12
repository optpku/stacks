/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Basic
public import ReasLib.CategoryTheory.Sites.MorphismOfSites

/-!
# Pullback on small Zariski sites

The small Zariski site is a full subcategory of an over-category on open
immersions. Its base-change functor is the generic morphism-property pullback
functor supplied by Mathlib.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {S T : Scheme.{u}}

/-- Base change along `f` on the small Zariski sites of schemes. -/
noncomputable abbrev smallZariskiPullback (f : T ⟶ S) :
    S.smallZariskiSite ⥤ T.smallZariskiSite :=
  MorphismProperty.Over.pullback @IsOpenImmersion ⊤ f

/-- Base change along a morphism of schemes is continuous for the small Zariski topologies. -/
instance smallZariskiPullback_isContinuous (f : T ⟶ S) :
    Functor.IsContinuous (smallZariskiPullback f)
      S.smallZariskiTopology T.smallZariskiTopology := sorry

/-- Base change along a morphism of schemes defines a morphism of small Zariski sites. -/
instance smallZariskiPullback_isMorphismOfSites (f : T ⟶ S) :
    IsMorphismOfSites S.smallZariskiTopology T.smallZariskiTopology
      (smallZariskiPullback f) := sorry

/-- Pulling back an open subscheme agrees with taking the inverse image of its open subset. -/
noncomputable def smallZariskiPullbackOpenFunctorIso (f : T ⟶ S) :
    smallZariskiOpenFunctor S ⋙ smallZariskiPullback f ≅
      TopologicalSpace.Opens.map f.base ⋙ smallZariskiOpenFunctor T :=
  NatIso.ofComponents
    (fun U ↦ MorphismProperty.Over.isoMk
      (pullbackSymmetry U.ι f ≪≫ pullbackRestrictIsoRestrict f U) (by
        change (pullbackSymmetry U.ι f).hom ≫
          (pullbackRestrictIsoRestrict f U).hom ≫ (f ⁻¹ᵁ U).ι =
            pullback.snd U.ι f
        simp))
    (by sorry)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of a chosen left Kan extension along small-Zariski base change is the
corresponding costructured-arrow colimit. -/
private noncomputable def smallZariskiLanEvaluationIsoColim
    (f : T ⟶ S) (X : T.smallZariskiSiteᵒᵖ) :
    (smallZariskiPullback f).op.lan ⋙
        (CategoryTheory.evaluation T.smallZariskiSiteᵒᵖ (Type (u + 1))).obj X ≅
      (Functor.whiskeringLeft _ _ (Type (u + 1))).obj
          (CostructuredArrow.proj (smallZariskiPullback f).op X) ⋙ colim :=
  NatIso.ofComponents (fun G =>
    IsColimit.coconePointUniqueUpToIso
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit
        (smallZariskiPullback f).op G X)
      (colimit.isColimit _)) (fun {G₁ G₂} φ => by
        apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit
          (smallZariskiPullback f).op G₁ X).hom_ext
        intro Y
        have h₁ := fun (G : S.smallZariskiSiteᵒᵖ ⥤ Type (u + 1)) =>
          IsColimit.comp_coconePointUniqueUpToIso_hom
            (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit
              (smallZariskiPullback f).op G X)
            (colimit.isColimit _) Y
        have h₂ := congr_app
          ((smallZariskiPullback f).op.lanUnit.naturality φ) Y.left
        dsimp at h₁ h₂ ⊢
        simp only [Category.assoc] at h₁ ⊢
        simp only [Functor.lan, Functor.lanUnit] at h₂ ⊢
        rw [reassoc_of% h₁, NatTrans.naturality_assoc, ← reassoc_of% h₂, h₁,
          ι_colimMap, Functor.whiskerLeft_app]
        rfl)

/-- Left Kan extension along small-Zariski base change preserves finite limits of
`Type (u + 1)`-valued presheaves. -/
private noncomputable instance smallZariskiPullbackLanPreservesFiniteLimits (f : T ⟶ S) :
    PreservesFiniteLimits
      ((smallZariskiPullback f).op.lan :
        (S.smallZariskiSiteᵒᵖ ⥤ Type (u + 1)) ⥤
          T.smallZariskiSiteᵒᵖ ⥤ Type (u + 1)) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u + 1}
  intro J _ _
  apply preservesLimitsOfShape_of_evaluation
    ((smallZariskiPullback f).op.lan :
      (S.smallZariskiSiteᵒᵖ ⥤ Type (u + 1)) ⥤
        T.smallZariskiSiteᵒᵖ ⥤ Type (u + 1)) J
  intro X
  -- Local instance justification (proof-local temporary data): the evaluation proof uses the
  -- filtered costructured-arrow category supplied pointwise by representable flatness.
  haveI : IsFiltered (CostructuredArrow (smallZariskiPullback f).op X) :=
    IsFiltered.of_equivalence
      (structuredArrowOpEquivalence (smallZariskiPullback f) (unop X))
  exact preservesLimitsOfShape_of_natIso
    (smallZariskiLanEvaluationIsoColim f X).symm

/-- The inverse-image functor induced by small-Zariski base change preserves finite limits. -/
noncomputable instance smallZariskiPullbackSheafPullbackPreservesFiniteLimits
    (f : T ⟶ S) [HasSheafify T.smallZariskiTopology (Type (u + 1))] :
    PreservesFiniteLimits
      ((smallZariskiPullback f).sheafPullback (Type (u + 1))
        S.smallZariskiTopology T.smallZariskiTopology) := by
  -- Local instance justification (defeq pin): pin the coefficient universe of the chosen
  -- left Kan extension before invoking the generic sheaf-pullback construction.
  letI : PreservesFiniteLimits
      ((smallZariskiPullback f).op.lan :
        (S.smallZariskiSiteᵒᵖ ⥤ Type (u + 1)) ⥤
          T.smallZariskiSiteᵒᵖ ⥤ Type (u + 1)) :=
    smallZariskiPullbackLanPreservesFiniteLimits f
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits
    (smallZariskiPullback f) (Type (u + 1))
      S.smallZariskiTopology T.smallZariskiTopology

end AlgebraicGeometry.Scheme
