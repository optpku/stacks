module

public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap67.Definition_67_45_2_Integral

/-!
# Lemma 70.15.1

A finite surjective morphism of algebraic spaces from an affine source forces
the target to be affine.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsAffine

/-- Lemma 70.15.1: if `f : X ⟶ Y` is a finite surjective morphism of algebraic
spaces over a scheme `S` and `X` is affine, then `Y` is affine. -/
@[stacks 07VS]
theorem of_isFinite_surjective {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Surjective f] [IsFinite f] [IsAffine X] : IsAffine Y :=
  sorry

end IsAffine

end AlgebraicGeometry.AlgebraicSpace
