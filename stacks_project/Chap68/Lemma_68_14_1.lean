module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Noetherian
import StacksCheckRecall

/-!
# Locally Noetherian decent algebraic spaces are quasi-separated

A locally Noetherian decent algebraic space is quasi-separated in the absolute
sense of Properties of Spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 68.14.1: Any locally Noetherian decent algebraic space is quasi-separated. -/
@[stacks 0BB6] #check
  (AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyQuasiSeparated.of_isLocallyNoetherian_isDecent :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [AlgebraicGeometry.AlgebraicSpace.IsLocallyNoetherian X]
      [AlgebraicGeometry.AlgebraicSpace.IsDecent X],
      AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyQuasiSeparated X)
