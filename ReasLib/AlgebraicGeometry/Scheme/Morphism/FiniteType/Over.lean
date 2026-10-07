module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Locally finite type morphisms in a slice category

This file records how local finite type behaves for the canonical objects of a scheme
slice category.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The structure morphism of `Over.mk p` is locally of finite type whenever `p` is. -/
instance instLocallyOfFiniteTypeOverMk {S X : Scheme.{u}} (p : X ⟶ S)
    [LocallyOfFiniteType p] : LocallyOfFiniteType (Over.mk p).hom := sorry

/-- The underlying scheme morphism of a composite in an over-category is locally of finite
type when the underlying morphisms of both factors are locally of finite type. -/
instance instLocallyOfFiniteTypeOverComp {S : Scheme.{u}} {X Y Z : Over S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyOfFiniteType f.left] [LocallyOfFiniteType g.left] :
    LocallyOfFiniteType (f ≫ g).left := sorry

/-- The underlying scheme morphism of a morphism in `Over S` is locally of finite type
whenever the source structure morphism is locally of finite type. -/
instance instLocallyOfFiniteTypeOverHom {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    [LocallyOfFiniteType X.hom] : LocallyOfFiniteType f.left := sorry

/-- The over-category morphism induced by the first map in a nested composite is locally
of finite type on underlying schemes when that first map is locally of finite type. -/
instance instLocallyOfFiniteTypeNestedOverHomMk
    {S : Scheme.{u}} {X : Over S} {Z Z' : Scheme.{u}}
    (j : Z' ⟶ Z) (i : Z ⟶ X.left) [LocallyOfFiniteType j] :
    LocallyOfFiniteType
      (Over.homMk j (Category.assoc j i X.hom).symm :
        Over.mk ((j ≫ i) ≫ X.hom) ⟶ Over.mk (i ≫ X.hom)).left := sorry

end AlgebraicGeometry
