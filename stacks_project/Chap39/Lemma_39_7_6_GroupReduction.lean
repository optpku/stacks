module

public import ReasLib.AlgebraicGeometry.GroupScheme.Reduction

open AlgebraicGeometry CategoryTheory

universe u

variable {k : Type u} [Field k] [PerfectField k]
variable (G : Over (Spec (.of k))) [GrpObj G]

/- Compatibility check for the former group-reduction implementation module. -/
#check (AlgebraicGeometry.Over.reductionClosedSubgroup G :
  AlgebraicGeometry.Scheme.ClosedSubgroup G)
