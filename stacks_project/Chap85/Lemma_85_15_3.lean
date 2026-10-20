module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Localization.SemiRepresentable
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.SemiRepresentableFamily
open CategoryTheory.GrothendieckTopology.SemiRepresentableLocalization

universe w v u

variable {C : Type u} [Category.{v} C]

/- Lemma 85.15.3 (1): for `K` in `SR(C)`, the functor `j_!` is the comparison
`comparison J K` into the slice over `sheafified J K`, and this comparison is an
equivalence `Sheaf (overTopology J K) (Type (max w v)) ⥤ Over (sheafified J K)`. -/
@[stacks 0D87] #check (CategoryTheory.GrothendieckTopology.SemiRepresentableLocalization.comparison.isEquivalence :
  ∀ (J : GrothendieckTopology C) (K : FormalCoproduct.{w} C)
    [HasWeakSheafify J (Type (max w v))]
    [HasWeakSheafify (overTopology J K) (Type (max w v))]
    [∀ G : (OverSite K)ᵒᵖ ⥤ Type (max w v),
      (SemiRepresentableFamily.forget K).op.HasLeftKanExtension G],
    Functor.IsEquivalence (comparison J K))

/- Lemma 85.15.3 (2): via the identification of (1), inverse image along `j` corresponds to
`Over.star` at `sheafified J K`, i.e. `F ↦ (F ⨯ F(K)^# ⟶ F(K)^#)`. -/
@[stacks 0D87] #check (CategoryTheory.GrothendieckTopology.SemiRepresentableLocalization.inverseImageComparison_isIso :
  ∀ (J : GrothendieckTopology C) (K : FormalCoproduct.{w} C)
    [HasWeakSheafify J (Type (max w v))]
    [HasWeakSheafify (overTopology J K) (Type (max w v))]
    [∀ G : (OverSite K)ᵒᵖ ⥤ Type (max w v),
      (SemiRepresentableFamily.forget K).op.HasLeftKanExtension G]
    [HasBinaryProducts (Sheaf J (Type (max w v)))],
    IsIso (inverseImageComparison J K))

/- Lemma 85.15.3 (3): for `φ : K ⟶ L` in `SR(C)`, inverse image along relocalization
corresponds via the identifications of (1) to `Over.pullback` along
`sheafifiedMap J φ : sheafified J K ⟶ sheafified J L`. -/
@[stacks 0D87] #check (CategoryTheory.GrothendieckTopology.SemiRepresentableLocalization.relocalizationInverseImageComparison_isIso :
  ∀ (J : GrothendieckTopology C) (K : FormalCoproduct.{w} C)
    [HasWeakSheafify J (Type (max w v))]
    [HasWeakSheafify (overTopology J K) (Type (max w v))]
    [∀ G : (OverSite K)ᵒᵖ ⥤ Type (max w v),
      (SemiRepresentableFamily.forget K).op.HasLeftKanExtension G]
    (L : FormalCoproduct.{w} C) (φ : K ⟶ L)
    [HasWeakSheafify (overTopology J L) (Type (max w v))]
    [∀ G : (OverSite L)ᵒᵖ ⥤ Type (max w v),
      (SemiRepresentableFamily.forget L).op.HasLeftKanExtension G]
    [∀ G : (OverSite K)ᵒᵖ ⥤ Type (max w v), (overMap φ).op.HasLeftKanExtension G]
    [HasPullbacksAlong (sheafifiedMap J φ)],
    IsIso (relocalizationInverseImageComparison J K L φ))
