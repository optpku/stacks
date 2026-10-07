module

public import Mathlib.Data.List.TFAE
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import stacks_project.Chap94.Lemma_94_14_3_Pullback
public import stacks_project.Chap100.Definition_100_5_1_Surjective
public import stacks_project.Chap101.Definition_101_14_2_UniversallyInjective
public import stacks_project.Chap101.Lemma_101_14_5_TwoArrow

/-!
# Characterizations of universally injective morphisms of algebraic stacks

A morphism of algebraic stacks is universally injective iff its relative
2-diagonal is surjective on points iff it lifts 2-arrows between
algebraically closed field-valued points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace UniversallyInjective

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]

/-- Lemma 101.14.5: for a morphism `f : X ⟶ Y` of algebraic stacks, the
following are equivalent: `UniversallyInjective f`; the relative 2-diagonal
`Hom.diagonal f : X ⟶ X ×_Y X` is surjective on points; and
`liftsAlgClosedTwoArrows f`. -/
@[stacks 0CPN]
theorem tfae (f : X ⟶ Y) :
    List.TFAE [UniversallyInjective f,
      Surjective (Hom.diagonal.{u + 1, u, u + 1} f),
      liftsAlgClosedTwoArrows f] :=
  sorry

/-- A morphism of algebraic stacks is universally injective if and only if its
relative 2-diagonal is surjective on points. -/
theorem iff_surjective_diagonal (f : X ⟶ Y) :
    UniversallyInjective f ↔ Surjective (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

/-- A morphism of algebraic stacks is universally injective if and only if it
lifts 2-arrows between algebraically closed field-valued points. -/
theorem iff_liftsAlgClosedTwoArrows (f : X ⟶ Y) :
    UniversallyInjective f ↔ liftsAlgClosedTwoArrows f :=
  sorry

/-- The relative 2-diagonal of a universally injective morphism of algebraic
stacks is surjective on points. -/
instance surjective_diagonal {f : X ⟶ Y} [UniversallyInjective f] :
    Surjective (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

end UniversallyInjective

end AlgebraicGeometry.AlgebraicStack
