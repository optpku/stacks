module

public import stacks_project.Chap61.Lemma_61_31_2_Inclusion
public import ReasLib.CategoryTheory.Sites.Topos.Retraction
public import ReasLib.CategoryTheory.Sites.Derived.SectionsComparison
public import ReasLib.CategoryTheory.Sites.FullyFaithful
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 61.31.2

The inclusion of nested chosen small pro-étale sites of a scheme satisfies the
hypotheses of Sites, Lemma 7.21.8. The induced morphisms of topoi compose to
the identity, the continuous direct image agrees with the cocontinuous inverse
image, and abelian cohomology is unchanged by the resulting restriction,
pushforward, and pullback.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

universe u v w

namespace AlgebraicGeometry.ChosenBigProetaleSite

variable {X Y : ChosenBigProetaleSite.{u, v}}
variable (S : X.carrier) (ι : X.carrier ⥤ Y.carrier)
variable (e : ι ⋙ Y.toScheme ≅ X.toScheme)
variable [ι.Full] [ι.Faithful]
variable [ι.IsContinuous X.toGrothendieck Y.toGrothendieck]

/-- Lemma 61.31.2 (1): the composite inverse image of the continuous and
cocontinuous morphisms of topoi attached to a nested small pro-étale inclusion
is naturally isomorphic to the identity. -/
@[stacks 098Y]
def smallNestedInclusion_comp_inverseImageIso
    [HasSheafify (smallTopology X S) (Type w)]
    [HasWeakSheafify (smallTopology Y (ι.obj S)) (Type w)]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ Type w,
      (smallNestedInclusion S ι e).op.HasLeftKanExtension P]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ Type w,
      (smallNestedInclusion S ι e).op.HasPointwiseLeftKanExtension P]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ Type w,
      (smallNestedInclusion S ι e).op.HasPointwiseRightKanExtension P] :
    (MorphismOfTopoiIn.comp
        ((smallNestedInclusion S ι e).morphismOfTopoiInOfContinuous
          (smallTopology X S) (smallTopology Y (ι.obj S)))
        ((smallNestedInclusion S ι e).morphismOfTopoiInOfCocontinuous
          (smallTopology X S) (smallTopology Y (ι.obj S)))).inverseImage ≅
      (MorphismOfTopoiIn.id (smallTopology X S)).inverseImage :=
  Retraction.compInverseImageIso (smallTopology X S)
    (smallTopology Y (ι.obj S)) (smallNestedInclusion S ι e)

/-- The nested small-inclusion retraction isomorphism is the Sites 7.21.8
inverse-image comparison. -/
theorem smallNestedInclusion_comp_inverseImageIso_hom
    [HasSheafify (smallTopology X S) (Type w)]
    [HasWeakSheafify (smallTopology Y (ι.obj S)) (Type w)]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ Type w,
      (smallNestedInclusion S ι e).op.HasLeftKanExtension P]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ Type w,
      (smallNestedInclusion S ι e).op.HasPointwiseLeftKanExtension P]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ Type w,
      (smallNestedInclusion S ι e).op.HasPointwiseRightKanExtension P] :
    (smallNestedInclusion_comp_inverseImageIso S ι e).hom =
      (Retraction.compInverseImageIso (smallTopology X S)
        (smallTopology Y (ι.obj S)) (smallNestedInclusion S ι e)).hom := sorry

/-- Lemma 61.31.2 (2): the cocontinuous inverse image of a nested small
pro-étale inclusion is naturally isomorphic to the continuous direct image. -/
@[stacks 098Y]
def smallNestedInclusion_pushforward_iso_inverseImage
    [HasSheafify (smallTopology X S) (Type w)]
    [HasWeakSheafify (smallTopology Y (ι.obj S)) (Type w)]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ Type w,
      (smallNestedInclusion S ι e).op.HasLeftKanExtension P]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ Type w,
      (smallNestedInclusion S ι e).op.HasPointwiseRightKanExtension P] :
    (((smallNestedInclusion S ι e).morphismOfTopoiInOfCocontinuous
        (smallTopology X S) (smallTopology Y (ι.obj S)))⁻¹) ≅
      (((smallNestedInclusion S ι e).morphismOfTopoiInOfContinuous
        (smallTopology X S) (smallTopology Y (ι.obj S)))_*) :=
  @asIso _ _ _ _
    (CocontinuousPullback.comparison.{w} (smallNestedInclusion S ι e)
      (smallTopology X S) (smallTopology Y (ι.obj S)))
    (CocontinuousPullback.comparison.isIso.{w} (smallNestedInclusion S ι e)
      (smallTopology X S) (smallTopology Y (ι.obj S)))

/-- The nested small-inclusion comparison `g⁻¹ ≅ f_*` is the canonical
cocontinuous-to-continuous comparison. -/
theorem smallNestedInclusion_pushforward_iso_inverseImage_hom
    [HasSheafify (smallTopology X S) (Type w)]
    [HasWeakSheafify (smallTopology Y (ι.obj S)) (Type w)]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ Type w,
      (smallNestedInclusion S ι e).op.HasLeftKanExtension P]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ Type w,
      (smallNestedInclusion S ι e).op.HasPointwiseRightKanExtension P] :
    (smallNestedInclusion_pushforward_iso_inverseImage S ι e).hom =
      CocontinuousPullback.comparison.{w} (smallNestedInclusion S ι e)
        (smallTopology X S) (smallTopology Y (ι.obj S)) := sorry

/-- Lemma 61.31.2 (3): for an abelian sheaf on the larger small pro-étale site,
degree-`p` cohomology agrees with cohomology of its restriction to the smaller
site. -/
@[stacks 098Y]
def smallNestedInclusion_cohomology_restrict
    [HasSheafify (smallTopology X S) AddCommGrpCat.{w}]
    [HasSheafify (smallTopology Y (ι.obj S)) AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor (smallTopology X S) AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor (smallTopology Y (ι.obj S)) AddCommGrpCat.{w}]
    [IsGrothendieckAbelian (Sheaf (smallTopology X S) AddCommGrpCat.{w})]
    [IsGrothendieckAbelian (Sheaf (smallTopology Y (ι.obj S)) AddCommGrpCat.{w})]
    [HasInjectiveResolutions (Sheaf (smallTopology X S) AddCommGrpCat.{w})]
    [HasInjectiveResolutions (Sheaf (smallTopology Y (ι.obj S)) AddCommGrpCat.{w})]
    (p : ℕ) (F' : Sheaf (smallTopology Y (ι.obj S)) AddCommGrpCat.{w}) :
    (((smallNestedInclusion S ι e).sheafPushforwardContinuous AddCommGrpCat.{w}
          (smallTopology X S) (smallTopology Y (ι.obj S)) ⋙
        Sheaf.Γ (smallTopology X S) AddCommGrpCat.{w}).rightDerived p).obj F' ≅
      ((Sheaf.Γ (smallTopology Y (ι.obj S)) AddCommGrpCat.{w}).rightDerived p).obj F' :=
  (SiteAbelianSectionsDerived.derivedGlobalSectionsIso
      (smallNestedInclusion S ι e) p (smallTerminalObject X S)
      (smallTerminalObjectIsTerminal X S)
      (smallNestedInclusion_obj_smallTerminalObject S ι e)).app F'

/-- The nested small-inclusion restriction comparison is the Sites 21.7.2
derived global-sections isomorphism at `F'`. -/
theorem smallNestedInclusion_cohomology_restrict_eq
    [HasSheafify (smallTopology X S) AddCommGrpCat.{w}]
    [HasSheafify (smallTopology Y (ι.obj S)) AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor (smallTopology X S) AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor (smallTopology Y (ι.obj S)) AddCommGrpCat.{w}]
    [IsGrothendieckAbelian (Sheaf (smallTopology X S) AddCommGrpCat.{w})]
    [IsGrothendieckAbelian (Sheaf (smallTopology Y (ι.obj S)) AddCommGrpCat.{w})]
    [HasInjectiveResolutions (Sheaf (smallTopology X S) AddCommGrpCat.{w})]
    [HasInjectiveResolutions (Sheaf (smallTopology Y (ι.obj S)) AddCommGrpCat.{w})]
    (p : ℕ) (F' : Sheaf (smallTopology Y (ι.obj S)) AddCommGrpCat.{w}) :
    smallNestedInclusion_cohomology_restrict S ι e p F' =
      (SiteAbelianSectionsDerived.derivedGlobalSectionsIso
          (smallNestedInclusion S ι e) p (smallTerminalObject X S)
          (smallTerminalObjectIsTerminal X S)
          (smallNestedInclusion_obj_smallTerminalObject S ι e)).app F' := sorry

/-- Lemma 61.31.2 (4): for an abelian sheaf on the smaller small pro-étale site,
degree-`p` cohomology agrees with cohomology of its cocontinuous pushforward to
the larger site. -/
@[stacks 098Y]
def smallNestedInclusion_cohomology_pushforward
    [HasSheafify (smallTopology X S) AddCommGrpCat.{w}]
    [HasSheafify (smallTopology Y (ι.obj S)) AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor (smallTopology X S) AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor (smallTopology Y (ι.obj S)) AddCommGrpCat.{w}]
    [IsGrothendieckAbelian (Sheaf (smallTopology X S) AddCommGrpCat.{w})]
    [IsGrothendieckAbelian (Sheaf (smallTopology Y (ι.obj S)) AddCommGrpCat.{w})]
    [HasInjectiveResolutions (Sheaf (smallTopology X S) AddCommGrpCat.{w})]
    [HasInjectiveResolutions (Sheaf (smallTopology Y (ι.obj S)) AddCommGrpCat.{w})]
    [((smallNestedInclusion S ι e).sheafPushforwardContinuous AddCommGrpCat.{w}
        (smallTopology X S) (smallTopology Y (ι.obj S))).PreservesInjectiveObjects]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (smallNestedInclusion S ι e).op.HasPointwiseRightKanExtension P]
    (p : ℕ) (F : Sheaf (smallTopology X S) AddCommGrpCat.{w}) :
    ((Sheaf.Γ (smallTopology X S) AddCommGrpCat.{w}).rightDerived p).obj F ≅
      ((Sheaf.Γ (smallTopology Y (ι.obj S)) AddCommGrpCat.{w}).rightDerived p).obj
        (((smallNestedInclusion S ι e).sheafPushforwardCocontinuous AddCommGrpCat.{w}
            (smallTopology X S) (smallTopology Y (ι.obj S))).obj F) :=
  ((Sheaf.Γ (smallTopology X S) AddCommGrpCat.{w}).rightDerived p).mapIso
      (asIso
        (((smallNestedInclusion S ι e).sheafAdjunctionCocontinuous AddCommGrpCat.{w}
            (smallTopology X S) (smallTopology Y (ι.obj S))).counit.app F)).symm ≪≫
    (RightDerived.precompObjIso
        ((smallNestedInclusion S ι e).sheafPushforwardContinuous AddCommGrpCat.{w}
          (smallTopology X S) (smallTopology Y (ι.obj S)))
        (Sheaf.Γ (smallTopology X S) AddCommGrpCat.{w}) p
        (((smallNestedInclusion S ι e).sheafPushforwardCocontinuous AddCommGrpCat.{w}
            (smallTopology X S) (smallTopology Y (ι.obj S))).obj F)).symm ≪≫
    smallNestedInclusion_cohomology_restrict S ι e p
      (((smallNestedInclusion S ι e).sheafPushforwardCocontinuous AddCommGrpCat.{w}
          (smallTopology X S) (smallTopology Y (ι.obj S))).obj F)

/-- The nested small-inclusion pushforward comparison is the fully faithful
counit identification, transported through derived global sections and composed
with the Sites 21.7.2 restriction isomorphism at the cocontinuous direct image. -/
theorem smallNestedInclusion_cohomology_pushforward_hom
    [HasSheafify (smallTopology X S) AddCommGrpCat.{w}]
    [HasSheafify (smallTopology Y (ι.obj S)) AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor (smallTopology X S) AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor (smallTopology Y (ι.obj S)) AddCommGrpCat.{w}]
    [IsGrothendieckAbelian (Sheaf (smallTopology X S) AddCommGrpCat.{w})]
    [IsGrothendieckAbelian (Sheaf (smallTopology Y (ι.obj S)) AddCommGrpCat.{w})]
    [HasInjectiveResolutions (Sheaf (smallTopology X S) AddCommGrpCat.{w})]
    [HasInjectiveResolutions (Sheaf (smallTopology Y (ι.obj S)) AddCommGrpCat.{w})]
    [((smallNestedInclusion S ι e).sheafPushforwardContinuous AddCommGrpCat.{w}
        (smallTopology X S) (smallTopology Y (ι.obj S))).PreservesInjectiveObjects]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (smallNestedInclusion S ι e).op.HasPointwiseRightKanExtension P]
    (p : ℕ) (F : Sheaf (smallTopology X S) AddCommGrpCat.{w}) :
    (smallNestedInclusion_cohomology_pushforward S ι e p F).hom =
      (((Sheaf.Γ (smallTopology X S) AddCommGrpCat.{w}).rightDerived p).mapIso
          (asIso
            (((smallNestedInclusion S ι e).sheafAdjunctionCocontinuous AddCommGrpCat.{w}
                (smallTopology X S) (smallTopology Y (ι.obj S))).counit.app F)).symm ≪≫
        (RightDerived.precompObjIso
            ((smallNestedInclusion S ι e).sheafPushforwardContinuous AddCommGrpCat.{w}
              (smallTopology X S) (smallTopology Y (ι.obj S)))
            (Sheaf.Γ (smallTopology X S) AddCommGrpCat.{w}) p
            (((smallNestedInclusion S ι e).sheafPushforwardCocontinuous AddCommGrpCat.{w}
                (smallTopology X S) (smallTopology Y (ι.obj S))).obj F)).symm ≪≫
        smallNestedInclusion_cohomology_restrict S ι e p
          (((smallNestedInclusion S ι e).sheafPushforwardCocontinuous AddCommGrpCat.{w}
              (smallTopology X S) (smallTopology Y (ι.obj S))).obj F)).hom := sorry

/-- Lemma 61.31.2 (5): for an abelian sheaf on the smaller small pro-étale site,
degree-`p` cohomology agrees with cohomology of its continuous pullback to the
larger site. -/
@[stacks 098Y]
def smallNestedInclusion_cohomology_pullback
    [HasSheafify (smallTopology X S) AddCommGrpCat.{w}]
    [HasSheafify (smallTopology Y (ι.obj S)) AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor (smallTopology X S) AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor (smallTopology Y (ι.obj S)) AddCommGrpCat.{w}]
    [IsGrothendieckAbelian (Sheaf (smallTopology X S) AddCommGrpCat.{w})]
    [IsGrothendieckAbelian (Sheaf (smallTopology Y (ι.obj S)) AddCommGrpCat.{w})]
    [HasInjectiveResolutions (Sheaf (smallTopology X S) AddCommGrpCat.{w})]
    [HasInjectiveResolutions (Sheaf (smallTopology Y (ι.obj S)) AddCommGrpCat.{w})]
    [((smallNestedInclusion S ι e).sheafPushforwardContinuous AddCommGrpCat.{w}
        (smallTopology X S) (smallTopology Y (ι.obj S))).PreservesInjectiveObjects]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (smallNestedInclusion S ι e).op.HasLeftKanExtension P]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (smallNestedInclusion S ι e).op.HasPointwiseLeftKanExtension P]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (smallNestedInclusion S ι e).op.HasPointwiseRightKanExtension P]
    (p : ℕ) (F : Sheaf (smallTopology X S) AddCommGrpCat.{w}) :
    ((Sheaf.Γ (smallTopology X S) AddCommGrpCat.{w}).rightDerived p).obj F ≅
      ((Sheaf.Γ (smallTopology Y (ι.obj S)) AddCommGrpCat.{w}).rightDerived p).obj
        (((smallNestedInclusion S ι e).sheafPullback AddCommGrpCat.{w}
            (smallTopology X S) (smallTopology Y (ι.obj S))).obj F) :=
  ((Sheaf.Γ (smallTopology X S) AddCommGrpCat.{w}).rightDerived p).mapIso
      (@asIso _ _ _ _
        (((smallNestedInclusion S ι e).sheafAdjunctionContinuous AddCommGrpCat.{w}
            (smallTopology X S) (smallTopology Y (ι.obj S))).unit.app F)
        (sheafAdjunctionContinuous_unit_app_isIso_of_fullyFaithful
          (smallTopology X S) (smallTopology Y (ι.obj S))
          (smallNestedInclusion S ι e) F)) ≪≫
    (RightDerived.precompObjIso
        ((smallNestedInclusion S ι e).sheafPushforwardContinuous AddCommGrpCat.{w}
          (smallTopology X S) (smallTopology Y (ι.obj S)))
        (Sheaf.Γ (smallTopology X S) AddCommGrpCat.{w}) p
        (((smallNestedInclusion S ι e).sheafPullback AddCommGrpCat.{w}
            (smallTopology X S) (smallTopology Y (ι.obj S))).obj F)).symm ≪≫
    smallNestedInclusion_cohomology_restrict S ι e p
      (((smallNestedInclusion S ι e).sheafPullback AddCommGrpCat.{w}
          (smallTopology X S) (smallTopology Y (ι.obj S))).obj F)

/-- The nested small-inclusion pullback comparison is the fully faithful unit
identification, transported through derived global sections and composed with
the Sites 21.7.2 restriction isomorphism at the continuous inverse image. -/
theorem smallNestedInclusion_cohomology_pullback_hom
    [HasSheafify (smallTopology X S) AddCommGrpCat.{w}]
    [HasSheafify (smallTopology Y (ι.obj S)) AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor (smallTopology X S) AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor (smallTopology Y (ι.obj S)) AddCommGrpCat.{w}]
    [IsGrothendieckAbelian (Sheaf (smallTopology X S) AddCommGrpCat.{w})]
    [IsGrothendieckAbelian (Sheaf (smallTopology Y (ι.obj S)) AddCommGrpCat.{w})]
    [HasInjectiveResolutions (Sheaf (smallTopology X S) AddCommGrpCat.{w})]
    [HasInjectiveResolutions (Sheaf (smallTopology Y (ι.obj S)) AddCommGrpCat.{w})]
    [((smallNestedInclusion S ι e).sheafPushforwardContinuous AddCommGrpCat.{w}
        (smallTopology X S) (smallTopology Y (ι.obj S))).PreservesInjectiveObjects]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (smallNestedInclusion S ι e).op.HasLeftKanExtension P]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (smallNestedInclusion S ι e).op.HasPointwiseLeftKanExtension P]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (smallNestedInclusion S ι e).op.HasPointwiseRightKanExtension P]
    (p : ℕ) (F : Sheaf (smallTopology X S) AddCommGrpCat.{w}) :
    (smallNestedInclusion_cohomology_pullback S ι e p F).hom =
      (((Sheaf.Γ (smallTopology X S) AddCommGrpCat.{w}).rightDerived p).mapIso
          (@asIso _ _ _ _
            (((smallNestedInclusion S ι e).sheafAdjunctionContinuous AddCommGrpCat.{w}
                (smallTopology X S) (smallTopology Y (ι.obj S))).unit.app F)
            (sheafAdjunctionContinuous_unit_app_isIso_of_fullyFaithful
              (smallTopology X S) (smallTopology Y (ι.obj S))
              (smallNestedInclusion S ι e) F)) ≪≫
        (RightDerived.precompObjIso
            ((smallNestedInclusion S ι e).sheafPushforwardContinuous AddCommGrpCat.{w}
              (smallTopology X S) (smallTopology Y (ι.obj S)))
            (Sheaf.Γ (smallTopology X S) AddCommGrpCat.{w}) p
            (((smallNestedInclusion S ι e).sheafPullback AddCommGrpCat.{w}
                (smallTopology X S) (smallTopology Y (ι.obj S))).obj F)).symm ≪≫
        smallNestedInclusion_cohomology_restrict S ι e p
          (((smallNestedInclusion S ι e).sheafPullback AddCommGrpCat.{w}
              (smallTopology X S) (smallTopology Y (ι.obj S))).obj F)).hom := sorry
end AlgebraicGeometry.ChosenBigProetaleSite
