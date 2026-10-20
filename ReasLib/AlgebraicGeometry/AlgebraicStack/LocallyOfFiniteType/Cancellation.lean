module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType

/-!
# Cancellation of local finite type against arbitrary postcomposition

If a composite morphism of algebraic stacks is locally of finite type, then so
is the first factor. No hypothesis is imposed on the second factor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType

/-- If a composite morphism of algebraic stacks is locally of finite type, then
so is the first factor. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFiniteType (f ≫ g)] : LocallyOfFiniteType f := sorry

end AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType
