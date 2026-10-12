/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.CategoryTheory.Preadditive.CompactObject

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SmallEtale.DerivedQCoh

/-- On an absolutely quasi-compact and quasi-separated algebraic space, a derived
module with quasicoherent cohomology is compact in the quasicoherent derived
category exactly when its underlying derived module is perfect. -/
theorem isCompactObject_iff_isPerfect {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] (object : DerivedQCoh X) :
    IsCompactObject object ↔ ModuleDerived.IsPerfect object.obj := sorry

end AlgebraicGeometry.AlgebraicSpace.SmallEtale.DerivedQCoh
