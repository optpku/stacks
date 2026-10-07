module

public import ReasLib.AlgebraicGeometry.DividedPowers.Scheme
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 60.7.2 -/
@[stacks 07I3] #check (DividedPowerScheme.{u} : Type (u + 1))

/- Definition 60.7.2 (2): morphisms preserve the ideal sheaves and the
divided-power operations on sections. -/
@[stacks 07I3] #check (DividedPowerScheme.Hom.{u} :
  DividedPowerScheme.{u} → DividedPowerScheme.{u} → Type u)
