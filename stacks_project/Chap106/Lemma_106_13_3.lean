/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import stacks_project.Chap101.Definition_101_9_1_Affine
public import stacks_project.Chap106.Definition_106_13_1_WellNighAffine

/-!
# Permanence of well-nigh affine algebraic stacks

A well-nigh affine algebraic stack that is an algebraic space is affine. An
algebraic stack affine over a well-nigh affine algebraic stack is itself
well-nigh affine.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsWellNighAffine

/-- Lemma 106.13.3 (1). Let the algebraic stack `X` be well-nigh affine. If `X`
is an algebraic space, then it is affine. -/
@[stacks 0DUN]
theorem isAffine {S : Scheme.{u}} {X : GroupoidsOver S} {F : AlgebraicSpace S}
    [AlgebraicStack X] [IsWellNighAffine X]
    (hF : Nonempty (X ≌ F.toGroupoids)) : AlgebraicSpace.IsAffine F :=
  sorry

/-- Lemma 106.13.3 (2). Let the algebraic stack `X` be well-nigh affine. If
`X' ⟶ X` is an affine morphism of algebraic stacks, then `X'` is well-nigh
affine. -/
@[stacks 0DUN]
theorem of_affine {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] [IsWellNighAffine X] (f : X' ⟶ X)
    [Groupoids.Hom.Affine f] : IsWellNighAffine X' :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsWellNighAffine

namespace AlgebraicGeometry.AlgebraicSpace.IsAffine

/-- A well-nigh affine algebraic space is affine. -/
instance of_isWellNighAffine {S : Scheme.{u}} (X : AlgebraicSpace S)
    [AlgebraicStack.IsWellNighAffine X.toGroupoids] : IsAffine X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsAffine
