module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Gerbe.Diagonal
import StacksCheckRecall

/-!
# Quasi-compactness of object diagonals along gerbes

If a morphism of algebraic stacks makes the source a gerbe over the target,
then quasi-compactness of the object diagonal of the source implies
quasi-compactness of the object diagonal of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

/- Lemma 101.28.14: Let `f : X ⟶ Y` be a morphism of algebraic stacks such
that `X` is a gerbe over `Y`. If the object diagonal `diagonal X` is
quasi-compact, then so is `diagonal Y`. -/
@[stacks 0DQL] #check
  (AlgebraicGeometry.AlgebraicStack.QuasiCompact.diagonal_of_gerbe :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y]
      (f : X ⟶ Y) [AlgebraicStack.Gerbe f]
      [AlgebraicStack.QuasiCompact (diagonal.{u + 1, u, u + 1} X)],
      AlgebraicStack.QuasiCompact (diagonal.{u + 1, u, u + 1} Y))
