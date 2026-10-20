module

public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Pretriangulated.Functor.TriangulatedStructure

@[expose] public section

/-!
# Triangulated Functors Induced by Localizer Morphisms

This leaf separates the formal descent of a triangulated structure through a localization from
the convenient instance used when all functors in the localization square are already equipped
with compatible shift and triangulated structures.
-/

noncomputable section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.LocalizerMorphism.localizedFunctor

open Limits Localization Pretriangulated

variable {C₁ : Type u₁} {C₂ : Type u₂} {D₁ : Type u₃} {D₂ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂]
  [Category.{v₃} D₁] [Category.{v₄} D₂]
  [HasZeroObject C₁] [HasZeroObject C₂] [HasZeroObject D₁] [HasZeroObject D₂]
  [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift D₁ ℤ] [HasShift D₂ ℤ]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D₁] [Preadditive D₂]
  [∀ n : ℤ, (shiftFunctor C₁ n).Additive]
  [∀ n : ℤ, (shiftFunctor C₂ n).Additive]
  [∀ n : ℤ, (shiftFunctor D₁ n).Additive]
  [∀ n : ℤ, (shiftFunctor D₂ n).Additive]
  [Pretriangulated C₁] [Pretriangulated C₂]
  [Pretriangulated D₁] [Pretriangulated D₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

/-- a triangulated structure descends across the source localization of a
localizer morphism whenever that localization reflects exactness by essential surjectivity on
arrows.  The source composite may carry any triangulated structure; no canonical choice is
forced at this layer. -/
@[stacks 05R7 "triangulated structure induced by a localizer morphism"]
theorem hasTriangulatedStructure
    (Φ : LocalizerMorphism W₁ W₂)
    (L₁ : C₁ ⥤ D₁) [L₁.IsLocalization W₁] [L₁.CommShift ℤ]
      [L₁.IsTriangulated] [L₁.mapArrow.EssSurj]
    (L₂ : C₂ ⥤ D₂) [L₂.IsLocalization W₂]
    (h : (Φ.functor ⋙ L₂).HasTriangulatedStructure) :
    (Φ.localizedFunctor L₁ L₂).HasTriangulatedStructure := sorry

/-- the functor induced by an exact morphism of shift-compatible localizers is
triangulated when both localization functors are triangulated and the source localization is
essentially surjective on arrows. -/
@[stacks 05R7 "exact localized functor of a localizer morphism"]
noncomputable instance isTriangulated
    (Φ : LocalizerMorphism W₁ W₂)
    [W₁.IsCompatibleWithShift ℤ] [W₂.IsCompatibleWithShift ℤ]
    [Φ.functor.CommShift ℤ] [Φ.functor.IsTriangulated]
    (L₁ : C₁ ⥤ D₁) [L₁.IsLocalization W₁]
    (L₂ : C₂ ⥤ D₂) [L₂.IsLocalization W₂]
    [L₁.CommShift ℤ] [L₂.CommShift ℤ]
    [L₁.IsTriangulated] [L₂.IsTriangulated] [L₁.mapArrow.EssSurj] :
    (Φ.localizedFunctor L₁ L₂).IsTriangulated := sorry


end CategoryTheory.LocalizerMorphism.localizedFunctor
