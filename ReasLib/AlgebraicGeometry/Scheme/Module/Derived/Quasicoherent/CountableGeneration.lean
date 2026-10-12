/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Countability
public import ReasLib.CategoryTheory.Pretriangulated.CompactObject.CountableGeneration

/-!
# Countable generation of derived quasicoherent modules

This module characterizes derived quasicoherent modules that are sequential homotopy colimits
of perfect derived modules in terms of countability of their cohomology on affine opens.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- On a quasi-compact quasi-separated scheme with countable rings of sections on affine opens,
a derived quasicoherent module is a sequential homotopy colimit of perfect derived modules if and
only if every cohomology sheaf has countable sections on every affine open. -/
theorem perfectHomotopyColimit_iff_countableAffineSections {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    (hX : ∀ U : X.affineOpens, Countable Γ(X, U))
    (K : AlgebraicGeometry.Scheme.ModuleDerived.Quasicoherent X) :
    sequentialHomotopyColimits
      (fun E : RingedSpace.ModuleDerived X.toRingedSpace ↦
        RingedSpace.ModuleDerived.IsPerfect E) K.obj ↔
      ∀ i : ℤ, ∀ U : X.affineOpens,
        Countable (RingedSpace.moduleSectionsOnOpen
          (RingedSpace.ModuleDerived.cohomologySheaf K.obj i) (U : X.Opens)) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
