module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pushout.Gluing

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Pushout.Gluing

/-- The unit of the pushout-gluing adjunction for a thickening and an affine morphism
of algebraic spaces is an isomorphism. -/
instance unitIsIso {S : Scheme.{u}} {X X' Y : AlgebraicSpace S}
    (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f] :
    IsIso (adjunction i f).unit :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Pushout.Gluing
