/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Spectral.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

/-!
# Punctured generizations of algebraic-space points

The strict generizations of a point of a decent locally Noetherian algebraic space,
with their induced topology, form a Noetherian, spectral, sober, Jacobson space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Points

/-- The set of points of `X` that specialize to `x`, other than `x` itself. -/
def puncturedGenerizations {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) :
    Set (Points X) :=
  {x' | x' ⤳ x ∧ x' ≠ x}

/-- A point lies in `puncturedGenerizations x` if and only if it specializes to `x` and is
distinct from `x`. -/
theorem mem_puncturedGenerizations {S : Scheme.{u}} {X : AlgebraicSpace S} {x x' : Points X} :
    x' ∈ puncturedGenerizations x ↔ x' ⤳ x ∧ x' ≠ x :=
  Iff.rfl

/-- The strict generizations of a point of a decent locally Noetherian algebraic space
form a Noetherian topological space. -/
instance instNoetherianSpace_puncturedGenerizations {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] [IsLocallyNoetherian X] (x : Points X) :
    TopologicalSpace.NoetherianSpace (puncturedGenerizations x) :=
  sorry

/-- The strict generizations of a point of a decent locally Noetherian algebraic space
form a spectral topological space. -/
instance instSpectralSpace_puncturedGenerizations {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] [IsLocallyNoetherian X] (x : Points X) :
    SpectralSpace (puncturedGenerizations x) :=
  sorry

/-- The strict generizations of a point of a decent locally Noetherian algebraic space
form a sober topological space. -/
theorem puncturedGenerizations_sober {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] [IsLocallyNoetherian X] {x : Points X} :
    T0Space (puncturedGenerizations x) ∧ QuasiSober (puncturedGenerizations x) :=
  ⟨inferInstance, inferInstance⟩

/-- The strict generizations of a point of a decent locally Noetherian algebraic space
form a Jacobson topological space. -/
instance instJacobsonSpace_puncturedGenerizations {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] [IsLocallyNoetherian X] (x : Points X) :
    JacobsonSpace (puncturedGenerizations x) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Points
