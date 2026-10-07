module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Point
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Site
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Quasi-coherent modules on a ringed point

Every module sheaf on a one-point ringed space admits a global free presentation and is therefore
quasi-coherent. Registering this fact once keeps associated-module constructions free of local
instances.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.RingedPoint.Module

variable (R : Type u) [CommRing R]

/-- Every module sheaf on `RingedPoint.of R` is quasi-coherent. -/
@[stacks 01BH "quasi-coherent modules on a ringed point"]
instance isQuasicoherent (G : (RingedPoint.of R).Modules) : G.IsQuasicoherent := sorry

end AlgebraicGeometry.RingedPoint.Module
