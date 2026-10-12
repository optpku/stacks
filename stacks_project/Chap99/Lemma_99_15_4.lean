/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap99.Lemma_99_15_2
public import stacks_project.Chap108.Lemma_108_4_8_Algebraic

/-!
# Lemma 99.15.4

The diagonal of `Curves` is representable by algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces
open AlgebraicGeometry.GroupScheme
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces
namespace Curves

/-- Lemma 99.15.4: the diagonal
`Δ : Curves ⟶ Curves × Curves` is representable by algebraic spaces. -/
@[stacks 0D53]
theorem relativelyRepresentableByAlgebraicSpaces_diagonal (S : Scheme.{u}) :
    Classifying.relativelyRepresentableByAlgebraicSpaces
      (CohStack.diagonal (toGroupoids S)) :=
  sorry

end Curves
end AlgebraicGeometry.AlgebraicSpace.Spaces
