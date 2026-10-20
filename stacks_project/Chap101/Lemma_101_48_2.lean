module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Decent
import StacksCheckRecall

/-!
# Quasi-separated algebraic stacks are decent

A quasi-separated algebraic stack is decent. More generally, quasi-compactness of
the diagonal is enough.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.48.2: A quasi-separated algebraic stack is decent. More generally,
an algebraic stack with quasi-compact absolute diagonal is decent. -/
@[stacks 0GW2] #check
  (AlgebraicGeometry.AlgebraicStack.IsDecent.of_quasiCompact_diagonal :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
      (h_quasiCompact :
        Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact (Spec (.of (ULift.{u} ℤ))))
          (diagonal.{u + 1, u, u + 1} (viewedOverSpecZ X))),
      IsDecent X)

#check (AlgebraicGeometry.AlgebraicStack.instIsDecent_of_isQuasiSeparated :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] [IsQuasiSeparated X],
    IsDecent X)

end AlgebraicGeometry.AlgebraicStack
