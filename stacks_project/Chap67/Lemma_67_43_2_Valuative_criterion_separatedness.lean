module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.ValuativeCriterion
import StacksCheckRecall

/-!
# Quasi-separated morphisms with uniqueness are separated

A quasi-separated morphism of algebraic spaces that satisfies uniqueness in the
valuative criterion is separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.43.2 (Valuative criterion separatedness) -/
@[stacks 03KV] #check
  (AlgebraicGeometry.AlgebraicSpace.Separated.of_valuativeCriterion :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicSpace.QuasiSeparated f]
      [AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.Uniqueness f],
      AlgebraicGeometry.AlgebraicSpace.Separated f)
