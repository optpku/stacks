module

public import stacks_project.Chap90.Definition_90_25_1_Groupoid
public import stacks_project.Chap90.Definition_90_25_1_Quotient
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Presentations of categories cofibered in groupoids

A presentation of a category cofibered in groupoids F by a groupoid in functors
(U, R, s, t, c) is an equivalence φ : [U/R] ⟶ F of categories cofibered in groupoids
over C.
-/

@[expose] public section

open CategoryTheory
open scoped Bicategory BasedFunctor

universe u v w

variable {C : Type u} [Category.{v} C]

namespace CategoryTheory.GroupoidInFunctors

/-- Definition 90.25.1: a presentation of a category cofibered in groupoids `F` by a
groupoid in functors `G = (U, R, s, t, c)` is an equivalence `φ : G.quotient ⟶ F` of
categories cofibered in groupoids over `C`. -/
@[stacks 06KX]
abbrev IsPresentation (G : GroupoidInFunctors.{u, v, w} C)
    (F : CofiberedCategoryOver.Groupoids C)
    (φ : G.quotient ⟶ F) : Prop :=
  BasedFunctor.IsEquivalence (CofiberedCategoryOver.Groupoids.toBasedFunctor φ)

/-- A morphism `φ : [U/R] ⟶ F` is a presentation if and only if it is an equivalence of
categories cofibered in groupoids over `C`. -/
theorem isPresentation_iff (G : GroupoidInFunctors.{u, v, w} C)
    (F : CofiberedCategoryOver.Groupoids C) (φ : G.quotient ⟶ F) :
    IsPresentation G F φ ↔
      BasedFunctor.IsEquivalence (CofiberedCategoryOver.Groupoids.toBasedFunctor φ) := sorry

/-- The identity morphism of `[U/R]` is a presentation of `[U/R]` by `G`. -/
theorem isPresentation_id (G : GroupoidInFunctors.{u, v, w} C) :
    IsPresentation G (quotient G) (𝟙 (quotient G)) := sorry

end CategoryTheory.GroupoidInFunctors
