module

public import ReasLib.AlgebraicGeometry.HomStack.Basic

open CategoryTheory AlgebraicGeometry

universe u

/- Mapping stacks with scheme domain. -/
#check (AlgebraicGeometry.GroupoidsOver.homStack :
    ∀ {S : Scheme.{u}} (X : Over S) (Z : GroupoidsOver S), GroupoidsOver S)
