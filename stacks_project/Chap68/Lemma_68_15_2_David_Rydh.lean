module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent.LocallySeparated
import StacksCheckRecall

/-!
# Locally separated algebraic spaces are decent

A locally separated algebraic space, in the absolute sense of
Definition 66.3.1, is decent.
-/

@[expose] public section

universe u

/- Lemma 68.15.2 (David Rydh): A locally separated algebraic space, in the
absolute sense of Definition 66.3.1, is decent. -/
@[stacks 088J] #check
  (AlgebraicGeometry.AlgebraicSpace.instIsDecent_of_isAbsolutelyLocallySeparated :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S)
      [AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyLocallySeparated X],
      AlgebraicGeometry.AlgebraicSpace.IsDecent X)
