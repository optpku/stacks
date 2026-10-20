module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Sites.Family.Simplicial.Augmentation

/-!
# Lemma 85.16.1

Degree-zero localization defines a case-B augmentation. Its stage and total
morphisms of topoi identify with localization through their direct images and
the inverse-image mates under the displayed adjunctions.
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]

/- Lemma 85.16.1 (1): degree-zero localization is an augmentation of the
simplicial localization site for the selected covers of the original site. -/
@[stacks 0D8B] #check (CategoryTheory.SemiRepresentableFamily.forget_isAugmentation :
  ∀ (K : SimplicialObject (FormalCoproduct.{w} C)) (P : Precoverage C) [P.IsSite],
    Grothendieck.IsAugmentation (overSiteDiagram K) (overSiteSelectedPrecoverage P K) P
      (forget (K.obj (op ⦋0⦌))))

/- The augmentation compatibility holds for every pair of zero-simplex operators. -/
#check (CategoryTheory.SemiRepresentableFamily.forget_comp_overMap_eq :
  ∀ (K : SimplicialObject (FormalCoproduct.{w} C)) {n : SimplexCategory} (φ ψ : ⦋0⦌ ⟶ n),
    overMap (K.map φ.op) ⋙ forget (K.obj (op ⦋0⦌)) =
      overMap (K.map ψ.op) ⋙ forget (K.obj (op ⦋0⦌)))

/- The stage presenting functor is the generic case-B stage composite. -/
#check (CategoryTheory.SemiRepresentableFamily.stageForget_eq_stageFunctor :
  ∀ (K : SimplicialObject (FormalCoproduct.{w} C)) (n : SimplexCategory),
    stageForget K n = Grothendieck.IsAugmentation.stageFunctor (overSiteDiagram K)
      (forget (K.obj (op ⦋0⦌))) n)

/- Lemma 85.16.1 (2): the stage augmentation and localization morphisms
have canonically isomorphic direct images. -/
@[stacks 0D8B] #check (CategoryTheory.SemiRepresentableFamily.stageTopos_iso_localizationMorphism :
  ∀ (J : GrothendieckTopology C) (K : SimplicialObject (FormalCoproduct.{w} C))
    [∀ n : SimplexCategoryᵒᵖ, HasSheafify (overTopology J (K.obj n)) (Type (max w u v))]
    [∀ (n : SimplexCategory) (P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ Type (max w u v)),
      (stageForget K n).op.HasPointwiseRightKanExtension P]
    [∀ (n : SimplexCategoryᵒᵖ) (P : (OverSite (K.obj n))ᵒᵖ ⥤ Type (max w u v)),
      (forget (K.obj n)).op.HasPointwiseRightKanExtension P]
    (n : SimplexCategory),
    (stageTopos J K n).pushforward ≅
      (localizationMorphism J (K.obj (op n))).pushforward)

/- The inverse-image comparison is the mate under the geometric adjunctions. -/
#check (CategoryTheory.SemiRepresentableFamily.stageTopos_inverseImage_iso_localizationMorphism :
  ∀ (J : GrothendieckTopology C) (K : SimplicialObject (FormalCoproduct.{w} C))
    [∀ n : SimplexCategoryᵒᵖ, HasSheafify (overTopology J (K.obj n)) (Type (max w u v))]
    [∀ (n : SimplexCategory) (P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ Type (max w u v)),
      (stageForget K n).op.HasPointwiseRightKanExtension P]
    [∀ (n : SimplexCategoryᵒᵖ) (P : (OverSite (K.obj n))ᵒᵖ ⥤ Type (max w u v)),
      (forget (K.obj n)).op.HasPointwiseRightKanExtension P]
    (n : SimplexCategory),
    (stageTopos J K n).inverseImage ≅
      (localizationMorphism J (K.obj (op n))).inverseImage)

/- Lemma 85.16.1 (3): the total augmentation and total localization morphisms
have canonically isomorphic direct images. -/
@[stacks 0D8B] #check (CategoryTheory.SemiRepresentableFamily.totalTopos_iso_totalLocalization :
  ∀ (J : GrothendieckTopology C) (K : SimplicialObject (FormalCoproduct.{w} C))
    [HasSheafify (overSiteTotalTopology J K) (Type (max w u v))]
    [∀ P : (Grothendieck (overSiteDiagram K))ᵒᵖ ⥤ Type (max w u v),
      (totalForget K).op.HasPointwiseRightKanExtension P]
    [∀ P : (Grothendieck (overSiteDiagram K))ᵒᵖ ⥤ Type (max w u v),
      (augmentationTotalForget K).op.HasPointwiseRightKanExtension P],
    (totalTopos J K).pushforward ≅ (totalLocalization J K).pushforward)

/- The total inverse-image comparison is the mate under the geometric adjunctions. -/
#check (CategoryTheory.SemiRepresentableFamily.totalTopos_inverseImage_iso_totalLocalization :
  ∀ (J : GrothendieckTopology C) (K : SimplicialObject (FormalCoproduct.{w} C))
    [HasSheafify (overSiteTotalTopology J K) (Type (max w u v))]
    [∀ P : (Grothendieck (overSiteDiagram K))ᵒᵖ ⥤ Type (max w u v),
      (totalForget K).op.HasPointwiseRightKanExtension P]
    [∀ P : (Grothendieck (overSiteDiagram K))ᵒᵖ ⥤ Type (max w u v),
      (augmentationTotalForget K).op.HasPointwiseRightKanExtension P],
    (totalTopos J K).inverseImage ≅ (totalLocalization J K).inverseImage)

end CategoryTheory.SemiRepresentableFamily
