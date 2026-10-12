/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.LocallyQuasiFinite.Semicontinuity
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Finite

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyQuasiFinite

/-- If the geometric fibre-component count of a separated, locally finite-type,
locally quasi-finite, universally open morphism attains the finite maximum `d`,
then its `d`-level set is open. -/
theorem isOpen_geometricFiberComponentCount_eq_of_isGreatest
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [IsSeparated f] [UniversallyOpen f] (d : ℕ)
    (hd : IsGreatest (Set.range f.geometricFiberComponentCount) d) :
    IsOpen {y : Y | f.geometricFiberComponentCount y = d} := sorry

/-- The open locus where a scheme morphism's geometric fibre-component count
equals its attained finite maximum. -/
noncomputable def maximalFiberComponentCountLocus
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [IsSeparated f] [UniversallyOpen f] (d : ℕ)
    (hd : IsGreatest (Set.range f.geometricFiberComponentCount) d) : Y.Opens where
  carrier := {y : Y | f.geometricFiberComponentCount y = d}
  is_open' := isOpen_geometricFiberComponentCount_eq_of_isGreatest f d hd

/-- Membership in `maximalFiberComponentCountLocus f d hd` is equality of the
geometric fibre-component count with `d`. -/
@[simp]
theorem mem_maximalFiberComponentCountLocus
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [IsSeparated f] [UniversallyOpen f] (d : ℕ)
    (hd : IsGreatest (Set.range f.geometricFiberComponentCount) d) (y : Y) :
    y ∈ maximalFiberComponentCountLocus f d hd ↔
      f.geometricFiberComponentCount y = d := sorry

/-- Over the open locus where the finite maximum of the geometric fibre-component
count is attained, the restricted morphism is finite. -/
@[instance]
theorem instIsFiniteMaximalFiberComponentCountLocus
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [IsSeparated f] [UniversallyOpen f] (d : ℕ)
    (hd : IsGreatest (Set.range f.geometricFiberComponentCount) d) :
    IsFinite (f ∣_ maximalFiberComponentCountLocus f d hd) := sorry

end AlgebraicGeometry.LocallyQuasiFinite
