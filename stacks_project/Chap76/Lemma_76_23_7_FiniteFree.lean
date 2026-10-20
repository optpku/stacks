module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FiniteFree

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Finite freeness in an étale neighbourhood of a point of an algebraic space. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.finiteFreeEtaleAt :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}, X.Modules → Points X → Prop)
