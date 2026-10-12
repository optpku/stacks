/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Coherent
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Regular

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.TStructure

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

/-- A cohomologically bounded derived module with coherent cohomology on a regular
scheme is perfect. -/
theorem isPerfect_of_boundedCoherentCohomology_of_regular {X : Scheme.{u}}
    [Scheme.Regular X] (E : ModuleDerived X.toRingedSpace)
    (hE_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) E)
    (hE_bounded : (t.bounded : ObjectProperty (ModuleDerived X.toRingedSpace)) E) :
    IsPerfect E := sorry

namespace IsPerfect

/-- A perfect derived module on a Noetherian regular scheme has coherent cohomology
and is cohomologically bounded. -/
theorem boundedCoherentCohomology_of_regular {X : Scheme.{u}}
    [Scheme.Regular X] [IsNoetherian X] (E : ModuleDerived X.toRingedSpace)
    (hE : IsPerfect E) :
    DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) E ∧
      (t.bounded : ObjectProperty (ModuleDerived X.toRingedSpace)) E := sorry

end IsPerfect

end AlgebraicGeometry.RingedSpace.ModuleDerived
