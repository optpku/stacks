/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import stacks_project.Chap98.Definition_98_11_1_LimitPreserving
public import stacks_project.Chap100.Lemma_100_11_2_LocallyOfFiniteType
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty
import Mathlib.Tactic.CrossRefAttribute

/-!
# Diagonals of limit-preserving categories fibred in groupoids

If a category fibred in groupoids over `(Sch/S)_fppf` is limit preserving and
its absolute diagonal is representable by algebraic spaces, then that diagonal
is locally of finite type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids

/-- Lemma 98.11.4: let `S` be a scheme and let `X` be a category fibred in
groupoids over `(Sch/S)_fppf`. If the diagonal `Δ : X ⟶ X × X` is
representable by algebraic spaces and `X` is limit preserving, then `Δ` is
locally of finite type. -/
@[stacks 0CXI]
theorem locallyOfFiniteType_diagonal {S : Scheme.{u}} (X : GroupoidsOver S)
    [LimitPreserving X]
    (h_diag : relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X)) :
    Hom.LocallyOfFiniteType
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) :=
  sorry

/-- The absolute diagonal of a limit-preserving category fibred in groupoids
has the scheme-slice locally-of-finite-type property of algebraic spaces. -/
theorem has_locallyOfFiniteType_diagonal {S : Scheme.{u}} (X : GroupoidsOver S)
    [LimitPreserving X]
    (h_diag : relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X)) :
    Hom.has (@AlgebraicSpace.LocallyOfFiniteType S)
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) :=
  sorry

end AlgebraicGeometry.Groupoids
