module

public import Mathlib.Data.List.TFAE
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty

/-!
# Separated representable morphisms of algebraic stacks

A morphism of algebraic stacks representable by algebraic spaces is separated
in the scheme-slice sense of algebraic spaces if and only if its relative
2-diagonal is a closed immersion, equivalently proper, equivalently
universally closed.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- Lemma 101.3.5: Let `f : X ⟶ Y` be a morphism of algebraic stacks
representable by algebraic spaces. Then the following are equivalent: `f` is
separated, `Hom.diagonal f` is a closed immersion, `Hom.diagonal f` is proper,
or `Hom.diagonal f` is universally closed. -/
@[stacks 04YS]
theorem separated_tfae {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    List.TFAE
      [has (@AlgebraicSpace.Separated S) f,
        has (@AlgebraicSpace.IsClosedImmersion S)
          (Hom.diagonal.{u + 1, u, u + 1} f),
        has (@AlgebraicSpace.Proper S) (Hom.diagonal.{u + 1, u, u + 1} f),
        has (@AlgebraicSpace.UniversallyClosed S)
          (Hom.diagonal.{u + 1, u, u + 1} f)] :=
  sorry

/-- A morphism of algebraic stacks representable by algebraic spaces is
separated on scheme-slice tests if and only if its relative 2-diagonal is a
closed immersion. -/
theorem has_separated_iff_closedImmersion_diagonal {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    has (@AlgebraicSpace.Separated S) f ↔
      has (@AlgebraicSpace.IsClosedImmersion S)
        (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

/-- A morphism of algebraic stacks representable by algebraic spaces is
separated on scheme-slice tests if and only if its relative 2-diagonal is
proper. -/
theorem has_separated_iff_proper_diagonal {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    has (@AlgebraicSpace.Separated S) f ↔
      has (@AlgebraicSpace.Proper S) (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

/-- A morphism of algebraic stacks representable by algebraic spaces is
separated on scheme-slice tests if and only if its relative 2-diagonal is
universally closed. -/
theorem has_separated_iff_universallyClosed_diagonal {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    has (@AlgebraicSpace.Separated S) f ↔
      has (@AlgebraicSpace.UniversallyClosed S)
        (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
