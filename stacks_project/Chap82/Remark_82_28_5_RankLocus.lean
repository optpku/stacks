module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RankLocus

/-! Compatibility facade for the canonical public owner. -/

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Modules.rankOpenSubspace :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree E], ℕ → OpenSubspace X)
