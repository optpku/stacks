module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.InvariantFunctions

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
variable (P : PreRelation U) (φ : U ⟶ X)
variable (h_invariant : P.t ≫ φ = P.s ≫ φ)

#check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.invariantFunctions P φ h_invariant :
    Sheaf (smallEtaleTopology X.left) RingCat.{u})
