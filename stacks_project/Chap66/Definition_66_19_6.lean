module

public import stacks_project.Chap66.Definition_66_19_6_Neighborhood
public import stacks_project.Chap66.Definition_66_19_6_Stalk
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry Opposite

universe u

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/- Definition 66.19.6: let `S` be a scheme, let `X` be an algebraic space over `S`, let `F` be a
presheaf on `X_étale`, and let `x̄` be a geometric point of `X`. The stalk of `F` at `x̄` is the
colimit of `F(U)` over étale neighborhoods `(U, ū)` of `x̄` with `U` an object of `X_étale`. -/
@[stacks 04JY] #check (AlgebraicGeometry.AlgebraicSpace.GeometricPoint.stalk :
  AlgebraicSpace.GeometricPoint X → ((AlgebraicSpace.smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) →
    Type (u + 1))
