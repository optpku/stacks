module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType.Fppf
import StacksCheckRecall

/-!
# Descent of local finite type along representable fppf morphisms of algebraic stacks

If `X ⟶ Z` is locally of finite type and `X ⟶ Y` is representable by algebraic
spaces, surjective, flat, and locally of finite presentation, then `Y ⟶ Z` is
locally of finite type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.17.7: Let `X ⟶ Y ⟶ Z` be morphisms of algebraic stacks. Assume
`X ⟶ Z` is locally of finite type and that `X ⟶ Y` is representable by
algebraic spaces, surjective, flat, and locally of finite presentation. Then
`Y ⟶ Z` is locally of finite type. -/
@[stacks 06U8] #check
  (AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType.of_comp_of_fppf :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicStack.LocallyOfFiniteType (f ≫ g)]
    [Groupoids.Hom.Surjective f] [Groupoids.Hom.Flat f]
    [Groupoids.Hom.LocallyOfFinitePresentation f],
    AlgebraicStack.LocallyOfFiniteType g)
