module

public import ReasLib.CategoryTheory.Bicategory.DottedArrow.Construction
public import stacks_project.Chap106.Definition_106_8_1_FormallySmooth

/-!
# Reformulation of formal smoothness

A morphism of algebraic stacks is formally smooth if and only if every
first-order affine thickening diagram has a nonempty category of dotted arrows.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 106.8.2. A morphism `f : X ⟶ Y` of algebraic stacks is formally
smooth (Definition 106.8.1) if and only if for every diagram 106.8.1.1 and
`γ` the category of dotted arrows is nonempty. -/
@[stacks 0DNY]
theorem FormallySmooth.iff_nonempty_dottedArrow
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    FormallySmooth f ↔
      ∀ {T T' : Over S} [IsAffine T.left] [IsAffine T'.left]
        (i : T ⟶ T') [IsFirstOrderThickening i.left]
        (x : GroupoidsOver.slice T ⟶ X) (y : GroupoidsOver.slice T' ⟶ Y)
        (γ : overMap i ≫ y ≅ x ≫ f),
        Nonempty (DottedArrow
          (⟨GroupoidsOver.slice T, overMap i, x, γ⟩ :
            Bicategory.PseudoPullbackCone y f)) :=
  sorry

/-- A formally smooth morphism of algebraic stacks has a nonempty category of
dotted arrows on every first-order affine thickening square. -/
theorem FormallySmooth.nonempty_dottedArrow
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [FormallySmooth f]
    {T T' : Over S} [IsAffine T.left] [IsAffine T'.left]
    (i : T ⟶ T') [IsFirstOrderThickening i.left]
    (x : GroupoidsOver.slice T ⟶ X) (y : GroupoidsOver.slice T' ⟶ Y)
    (γ : overMap i ≫ y ≅ x ≫ f) :
    Nonempty (DottedArrow
      (⟨GroupoidsOver.slice T, overMap i, x, γ⟩ :
        Bicategory.PseudoPullbackCone y f)) :=
  sorry

/-- A morphism of algebraic stacks is formally smooth if every first-order
affine thickening square has a nonempty category of dotted arrows. -/
theorem FormallySmooth.of_nonempty_dottedArrow
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (h : ∀ {T T' : Over S} [IsAffine T.left] [IsAffine T'.left]
      (i : T ⟶ T') [IsFirstOrderThickening i.left]
      (x : GroupoidsOver.slice T ⟶ X) (y : GroupoidsOver.slice T' ⟶ Y)
      (γ : overMap i ≫ y ≅ x ≫ f),
      Nonempty (DottedArrow
        (⟨GroupoidsOver.slice T, overMap i, x, γ⟩ :
          Bicategory.PseudoPullbackCone y f))) :
    FormallySmooth f :=
  sorry

end AlgebraicGeometry.AlgebraicStack
