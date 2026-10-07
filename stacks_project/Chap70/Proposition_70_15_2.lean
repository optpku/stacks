module

public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_9_2_Closed
public import stacks_project.Chap67.Definition_67_20_2_Affine

/-!
# Proposition 70.15.2

A surjective universally closed morphism of algebraic spaces from an affine
source forces the target to be affine.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsAffine

/-- Proposition 70.15.2: if `f : X ⟶ Y` is a surjective universally closed
morphism of algebraic spaces over a scheme `S` and `X` is affine, then `Y` is
affine. -/
@[stacks 07VT]
theorem of_surjective_universallyClosed {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Surjective f] [UniversallyClosed f] [IsAffine X] : IsAffine Y :=
  sorry

end IsAffine

end AlgebraicGeometry.AlgebraicSpace
