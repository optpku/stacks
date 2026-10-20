module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Products of morphisms locally of finite type

This file records stability of local finite type for products in an over-category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The product of two schemes locally of finite type over the same base is locally of
finite type over that base. -/
instance locallyOfFiniteType_overProd {S : Scheme.{u}} (X Y : Over S)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] :
    LocallyOfFiniteType (X ⨯ Y).hom := sorry

end AlgebraicGeometry
