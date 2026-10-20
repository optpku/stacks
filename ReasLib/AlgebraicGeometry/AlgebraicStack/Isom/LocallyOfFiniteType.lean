module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Isom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Isom

/-- The structure morphism of the isomorphism algebraic space of two fibre
objects of an algebraic stack is locally of finite type. -/
instance locallyOfFiniteType_isomOverHom {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {T : Over S} (x y : X.p.Fiber T) :
    AlgebraicSpace.LocallyOfFiniteType (isomOverHom x y) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Isom
