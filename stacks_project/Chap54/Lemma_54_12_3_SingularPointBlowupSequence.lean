module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.SingularPointSequence

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- The finite singular-point blowup sequence is owned by the shared blowup API. -/
#check (AlgebraicGeometry.Scheme.SingularPointBlowupSequence :
  Scheme.{u} → Scheme.{u} → Type (u + 1))
