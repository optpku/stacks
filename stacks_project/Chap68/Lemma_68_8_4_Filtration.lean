module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Stratification.Finite

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check
  (AlgebraicGeometry.AlgebraicSpace.exists_finiteSchemeStratumFiltration :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsQuasiCompact X] [IsReasonable X],
      Nonempty (FiniteSchemeStratumFiltration X))

end AlgebraicGeometry.AlgebraicSpace
