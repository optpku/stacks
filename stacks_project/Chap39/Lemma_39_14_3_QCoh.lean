module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Module.Quasicoherent

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory

variable {S : Scheme.{u}} (G : GroupoidScheme S)

/- Compatibility bridge for the category of equivariant quasi-coherent modules on a
groupoid scheme. -/
#check (AlgebraicGeometry.GroupoidScheme.QCoh G : Cat)
