module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType

/-!
# Cancellation of local finite presentation against locally finite type postcomposition

If a composite morphism of algebraic stacks is locally of finite presentation and
the second factor is locally of finite type, then the first factor is locally of
finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation

/-- If a composite morphism of algebraic stacks is locally of finite presentation
and the second factor is locally of finite type, then the first factor is
locally of finite presentation. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ g)] [LocallyOfFiniteType g] :
    LocallyOfFinitePresentation f := sorry

end AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation
