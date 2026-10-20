module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeCriterion

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Existence :
  {S : Scheme.{u}} → {X Y : GroupoidsOver S} →
    [AlgebraicGeometry.AlgebraicStack X] → [AlgebraicGeometry.AlgebraicStack Y] →
    (X ⟶ Y) → Prop)
