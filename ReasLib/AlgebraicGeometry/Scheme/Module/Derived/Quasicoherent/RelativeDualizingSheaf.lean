/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.StructureSheaf

/-!
# Relative dualizing sheaf

The relative dualizing sheaf of a morphism is the degree `-1` cohomology of the
chosen right adjoint of derived pushforward applied to the derived structure
sheaf of the base.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- The relative dualizing sheaf of a morphism, as the degree `-1` cohomology of
the chosen relative dualizing complex. -/
noncomputable def relativeDualizingSheaf {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [(pushforwardCohomologyIn f).IsLeftAdjoint] : X.Modules :=
  RingedSpace.ModuleDerived.cohomologySheaf
    ((pushforwardCohomologyIn f).rightAdjoint.obj (structureSheaf S)).obj
    (-1)

end AlgebraicGeometry.Scheme.DerivedQCoh
