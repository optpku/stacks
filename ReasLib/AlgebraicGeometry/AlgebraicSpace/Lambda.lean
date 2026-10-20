module

public import ReasLib.AlgebraicGeometry.Scheme.Lambda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale

/-!
# Residue-field cardinal bound of an algebraic space

The cardinal bound of an algebraic space is computed on any surjective étale
scheme presentation.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Cardinal

namespace AlgebraicGeometry.AlgebraicSpace

/-- The cardinal `lambda X` of an algebraic space, as `lambda` of a chosen scheme
presenting `X` by a representable étale locally-surjective atlas. -/
noncomputable def lambda {S : Scheme.{u}} (X : AlgebraicSpace S) : Cardinal.{u} :=
  Scheme.lambda (Classical.choose X.atlas).left

/-- `lambda X` agrees with `lambda` of the underlying scheme of any surjective
étale presentation of `X`. -/
theorem lambda_spec {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (p : ofOver U ⟶ X) [Etale p] (hp : Function.Surjective (Points.map p)) :
    lambda X = Scheme.lambda U.left :=
  sorry

/-- On a scheme viewed as an algebraic space over `S`, `lambda` recovers the
scheme-level cardinal. -/
theorem lambda_ofOver {S : Scheme.{u}} (U : Over S) :
    lambda (ofOver U) = Scheme.lambda U.left :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
