module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Flat
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFinitePresentation

/-!
# Descent of local finite type along representable fppf morphisms of algebraic stacks
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType

/-- For composable morphisms `X ⟶ Y ⟶ Z` of algebraic stacks, if
`X ⟶ Z` is locally of finite type and `X ⟶ Y` is representable by
algebraic spaces, surjective, flat, and locally of finite presentation, then
`Y ⟶ Z` is locally of finite type. -/
theorem of_comp_of_fppf {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyOfFiniteType (f ≫ g)]
    [Groupoids.Hom.Surjective f] [Groupoids.Hom.Flat f]
    [Groupoids.Hom.LocallyOfFinitePresentation f] :
    LocallyOfFiniteType g :=
  sorry

end AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType
