module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.NormalizedSequence

@[expose] public section

open AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicSpace.NormalizedBlowupSequence :
  ∀ {S : Scheme.{u}}, AlgebraicSpace S → AlgebraicSpace S → Type (u + 1))
