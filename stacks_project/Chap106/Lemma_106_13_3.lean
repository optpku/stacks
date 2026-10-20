module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.WellNighAffine.Affine
import StacksCheckRecall

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

/- Lemma 106.13.3 (1). Let the algebraic stack `X` be well-nigh affine. If `X`
is an algebraic space, then it is affine. -/
@[stacks 0DUN] #check (AlgebraicGeometry.AlgebraicStack.IsWellNighAffine.isAffine :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} {F : AlgebraicSpace S}
      [AlgebraicStack X] [AlgebraicStack.IsWellNighAffine X],
      Nonempty (X ≌ F.toGroupoids) → AlgebraicSpace.IsAffine F)

/- Lemma 106.13.3 (2). Let the algebraic stack `X` be well-nigh affine. If
`X' ⟶ X` is an affine morphism of algebraic stacks, then `X'` is well-nigh
affine. -/
@[stacks 0DUN] #check (AlgebraicGeometry.AlgebraicStack.IsWellNighAffine.of_affine :
    ∀ {S : Scheme.{u}} {X X' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack.IsWellNighAffine X]
      (f : X' ⟶ X) [Groupoids.Hom.Affine f], AlgebraicStack.IsWellNighAffine X')

/- A well-nigh affine algebraic space is affine. -/
#check (AlgebraicGeometry.AlgebraicSpace.IsAffine.of_isWellNighAffine :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [AlgebraicStack.IsWellNighAffine X.toGroupoids], AlgebraicSpace.IsAffine X)
