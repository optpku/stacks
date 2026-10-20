module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Gerbe
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Decent

/-!
# Descent of decency along gerbes

If `f : X ⟶ Y` is a gerbe morphism of algebraic stacks and `X` is decent, then
`Y` is decent.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The target of a gerbe morphism of algebraic stacks with decent source is
decent. -/
theorem IsDecent.of_gerbe {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Gerbe f]
    [IsDecent X] : IsDecent Y :=
  sorry

end AlgebraicGeometry.AlgebraicStack
