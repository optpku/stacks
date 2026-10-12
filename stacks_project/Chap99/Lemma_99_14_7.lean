/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap99.Lemma_99_14_8_Groupoids

/-!
# Lemma 99.14.7

The diagonal of Polarized is representable by algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

/-- Lemma 99.14.7: the diagonal
`Δ : Polarized ⟶ Polarized × Polarized` is representable by algebraic spaces. -/
@[stacks 0D42]
theorem relativelyRepresentableByAlgebraicSpaces_diagonal :
    relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} toGroupoidsOverSpecZ) :=
  sorry

end AlgebraicGeometry.Polarized
