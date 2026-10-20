module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Surjective

/-!
# Descent of local finite presentation along fppf morphisms of algebraic stacks
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation

/-- For composable morphisms `X ⟶ Y ⟶ Z` of algebraic stacks, if
`X ⟶ Z` is locally of finite presentation and `X ⟶ Y` is surjective, flat,
and locally of finite presentation, then `Y ⟶ Z` is locally of finite
presentation. -/
theorem of_comp_of_fppf {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ g)]
    [Surjective f] [Flat f] [LocallyOfFinitePresentation f] :
    LocallyOfFinitePresentation g :=
  sorry

end AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation
