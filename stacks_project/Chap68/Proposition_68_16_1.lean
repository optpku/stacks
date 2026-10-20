module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.Decent
import StacksCheckRecall

/-!
# Valuative criterion for universal closedness of decent algebraic spaces

A quasi-compact morphism of algebraic spaces with decent source is universally
closed if and only if it satisfies the existence part of the valuative
criterion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

open AlgebraicGeometry.AlgebraicSpace

/- Proposition 68.16.1: Let `f : X ⟶ Y` be a quasi-compact morphism of
algebraic spaces over a scheme `S`, and assume `X` is decent. Then `f` is
universally closed if and only if the existence part of the valuative
criterion holds. -/
@[stacks 03KJ] #check
  (AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.iff_existence_of_isDecent :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiCompact f] [IsDecent X],
      UniversallyClosed f ↔ ValuativeCriterion.Existence f)

#check
  (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.Existence.of_universallyClosed_of_isDecent :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiCompact f] [IsDecent X] [UniversallyClosed f],
      ValuativeCriterion.Existence f)
