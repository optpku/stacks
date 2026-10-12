/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.BrownRepresentability
public import ReasLib.CategoryTheory.Pretriangulated.CompactObject.Generation
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Coproduct
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Compact
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Generation

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- For a quasi-compact and quasi-separated scheme, the inclusion of derived modules with
quasi-coherent cohomology into all derived modules admits a right adjoint. -/
instance inclusionIsLeftAdjoint (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] :
    (Scheme.ModuleDerived.Quasicoherent.inclusion X).IsLeftAdjoint := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
