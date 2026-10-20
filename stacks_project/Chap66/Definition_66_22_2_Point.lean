module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.SmallEtalePoint
public import stacks_project.Chap66.Definition_66_19_1_GeometricPoint

/-!
# Small étale site points of algebraic spaces

A geometric point of an algebraic space determines a point of the small étale site, whose
fiber at an étale scheme `U` over `X` is the type of lifts of the geometric point through
`U` in `Over S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The fiber of `toSmallEtalePoint xbar` at an étale scheme `U` over `X` is the type of
scheme-over-`S` lifts of `xbar` through `U`. -/
theorem toSmallEtalePoint_fiber_obj (xbar : GeometricPoint X) (U : smallEtaleSite X) :
    (toSmallEtalePoint xbar).fiber.obj U = OverLift xbar U :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint
