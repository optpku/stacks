/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty

/-!
# Locally separated representable morphisms of algebraic stacks

A morphism of algebraic stacks representable by algebraic spaces is locally
separated in the scheme-slice sense of algebraic spaces if and only if its
relative 2-diagonal is an immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- Lemma 101.3.7: Let `f : X ⟶ Y` be a morphism of algebraic stacks
representable by algebraic spaces. Then the following are equivalent: `f` is
locally separated, and `Hom.diagonal f` is an immersion. -/
@[stacks 04YU]
theorem locallySeparated_tfae {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    List.TFAE
      [has (@AlgebraicSpace.LocallySeparated S) f,
        has (@AlgebraicSpace.IsImmersion S)
          (Hom.diagonal.{u + 1, u, u + 1} f)] :=
  sorry

/-- A morphism of algebraic stacks representable by algebraic spaces is
locally separated on scheme-slice tests if and only if its relative 2-diagonal
is an immersion. -/
theorem has_locallySeparated_iff_immersion_diagonal {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    has (@AlgebraicSpace.LocallySeparated S) f ↔
      has (@AlgebraicSpace.IsImmersion S)
        (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
