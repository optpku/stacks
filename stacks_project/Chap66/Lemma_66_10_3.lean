module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.LocalRing
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/- Lemma 66.10.3: let `S` be a scheme and let `X` be an algebraic space over `S`. The
 dimension of `X` equals the supremum of the dimensions of the local rings of `X`. -/
@[stacks 0BAN] #check
  (AlgebraicGeometry.AlgebraicSpace.dimension_eq_iSup_localRingDimAt X :
    dimension X = ⨆ x : Points X, localRingDimAt x)

#check (AlgebraicGeometry.AlgebraicSpace.dimension_eq_iSup_dimensionAt X :
  dimension X = ⨆ x : Points X, dimensionAt x)

end AlgebraicGeometry.AlgebraicSpace
