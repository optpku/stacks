module

public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition

/-!
# Module sheaves on locally ringed spaces

This leaf supplies the direct locally-ringed-space spelling of the module category.  Fiber and
stalk-carrier constructions live in the focused `Module.FiberRank` leaf.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

/-- The category of sheaves of modules over the structure sheaf of a locally ringed space. -/
abbrev Modules (X : LocallyRingedSpace.{u}) :=
  X.toRingedSpace.Modules

end AlgebraicGeometry.LocallyRingedSpace
