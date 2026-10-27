/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Defs.Filter
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.FieldPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints.Relative.Locus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange

/-!
# Specialization of relatively associated points into a fibre

For a finite-type quasi-coherent module on a decent algebraic space locally of
finite type over a scheme, flatness along a fibre ensures that a relatively
associated point whose closure meets the fibre specializes to a relatively
associated point in that fibre.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.relativeAssassin

/-- On a decent algebraic space locally of finite type over a scheme, a relatively
associated point of a finite-type quasi-coherent module that specializes into a
fibre along which the module is flat specializes to a relatively associated point
lying in that fibre. -/
theorem exists_mem_fiber_of_specializes {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] [LocallyOfFiniteType (SchemeRealization.toBase X)] (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (s : S) {x' : Points X}
    (hx' : x' ∈ relativeAssassin (SchemeRealization.toBase X) ℱ)
    (hflat : ∀ z : Points X, Points.base z = s →
      flatOverAt ℱ (SchemeRealization.toBase X) z)
    (hmeets : ∃ t : Points X, Points.base t = s ∧ Specializes x' t) :
    ∃ x : Points X,
      Points.base x = s ∧ x ∈ relativeAssassin (SchemeRealization.toBase X) ℱ ∧
        Specializes x' x :=
  sorry

/-- On a decent algebraic space locally of finite type over a scheme, the closure
of a relatively associated point of a finite-type quasi-coherent module meets
the relative assassin inside any fibre it meets, provided the module is flat at
every point of that fibre. -/
theorem exists_mem_fiber_of_closure_meets {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] [LocallyOfFiniteType (SchemeRealization.toBase X)] (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (s : S) {x' : Points X}
    (hx' : x' ∈ relativeAssassin (SchemeRealization.toBase X) ℱ)
    (hflat : ∀ z : Points X, Points.base z = s →
      flatOverAt ℱ (SchemeRealization.toBase X) z)
    (hmeets : (closure {x'} ∩ Points.base ⁻¹' {s}).Nonempty) :
    (closure {x'} ∩ relativeAssassin (SchemeRealization.toBase X) ℱ ∩
      Points.base ⁻¹' {s}).Nonempty :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.relativeAssassin
