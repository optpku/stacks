module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType.Cancellation

/-!
# Cancellation of local finite type against arbitrary postcomposition

If a composite morphism of algebraic spaces is locally of finite type, then so
is the first factor. No hypothesis is imposed on the second factor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
      [LocallyOfFiniteType (f ≫ g)], LocallyOfFiniteType f)
