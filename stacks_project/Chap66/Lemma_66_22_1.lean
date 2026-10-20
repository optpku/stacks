module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Neighborhood
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LocalRing
import StacksCheckRecall

open AlgebraicGeometry

universe u

/- Lemma 66.22.1 (1): the étale-site stalk `𝒪_{X, xbar}` of the structure sheaf of `X`
identifies with the étale-site stalk `𝒪_{U, ubar}` of a scheme étale neighbourhood
`(U, ubar)` of `xbar`. -/
@[stacks 04KF] #check
  (AlgebraicGeometry.AlgebraicSpace.etaleLocalRing_etaleNeighborhood :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} →
      {xbar : AlgebraicSpace.GeometricPoint X} →
      (N : AlgebraicSpace.GeometricPoint.SmallEtaleNeighborhood xbar) →
      AlgebraicSpace.etaleLocalRing X xbar ≃+*
        Scheme.etaleLocalRing N.scheme
          (AlgebraicSpace.GeometricPoint.SmallEtaleNeighborhood.schemeGeometricPoint N))

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {xbar : AlgebraicSpace.GeometricPoint X}
variable (N : AlgebraicSpace.GeometricPoint.SmallEtaleNeighborhood xbar)

/- Lemma 66.22.1 (2): the étale-site stalk `𝒪_{U, ubar}` is a strict henselization of the
Zariski local ring of `U` at the center `u` of `ubar`. -/
@[stacks 04KF] #check (AlgebraicGeometry.Scheme.etaleLocalRing.isStrictHenselizationOf N.scheme
  (AlgebraicSpace.GeometricPoint.SmallEtaleNeighborhood.schemeGeometricPoint N) :
    IsStrictHenselizationOf (N.scheme.presheaf.stalk N.center)
      (Scheme.etaleLocalRing.asAlgebra N.scheme
        (AlgebraicSpace.GeometricPoint.SmallEtaleNeighborhood.schemeGeometricPoint N)))
