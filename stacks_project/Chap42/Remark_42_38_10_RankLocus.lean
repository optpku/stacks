module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.RankLocus

@[expose] public section

open AlgebraicGeometry TopologicalSpace

universe u

/- A compatibility check for the clopen rank-locus construction. -/
#check (AlgebraicGeometry.Scheme.Modules.rankClopen :
  ∀ {X : Scheme.{u}} (E : X.Modules) [E.IsFiniteLocallyFree] (r : ℕ), Clopens X)
