module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Isom

/-!
# Structure morphisms of isomorphism algebraic spaces

The structure morphism of the Isom algebraic space over its fibre base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids

universe u

#check (AlgebraicGeometry.AlgebraicStack.Isom.isomOverHom :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T : Over S} (x y : X.p.Fiber T),
    AlgebraicGeometry.AlgebraicStack.Isom.isomSpace x y ⟶
      AlgebraicGeometry.AlgebraicStack.Isom.selfSpace T)
