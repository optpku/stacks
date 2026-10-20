module

public import stacks_project.Chap66.Definition_66_19_1_GeometricPoint
import StacksCheckRecall

universe u

/- Definition 66.19.1 (1): a geometric point of an algebraic space `X` over a scheme `S` is a
morphism `Spec(k) ⟶ X` over `S` from the spectrum of an algebraically closed field. -/
@[stacks 0486] #check
  (AlgebraicGeometry.AlgebraicSpace.GeometricPoint :
    {S : AlgebraicGeometry.Scheme.{u}} →
      AlgebraicGeometry.AlgebraicSpace S → Type (u + 1))

/- Definition 66.19.1 (2): every geometric point `xbar` has a corresponding image point
`xbar.image` in `|X|`; we say that `xbar` is a geometric point lying over `x` when
`xbar.liesOver x`. -/
@[stacks 0486] #check
  (AlgebraicGeometry.AlgebraicSpace.GeometricPoint.image :
    {S : AlgebraicGeometry.Scheme.{u}} →
      {X : AlgebraicGeometry.AlgebraicSpace S} →
        AlgebraicGeometry.AlgebraicSpace.GeometricPoint X →
          AlgebraicGeometry.AlgebraicSpace.Points X)
