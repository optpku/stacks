module

public import ReasLib.SetTheory.Cardinal.Bound

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The cardinal bound given by the maximum of the countable power and the successor. -/
noncomputable abbrev bound (kappa : Cardinal.{u}) : Cardinal.{u} :=
  Cardinal.countableSuccBound kappa

end AlgebraicGeometry.Scheme
