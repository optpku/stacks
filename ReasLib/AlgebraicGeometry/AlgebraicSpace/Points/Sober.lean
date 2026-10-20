/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Transfer
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.Topology.Sober.GenericPoint

/-!
# Sobriety of algebraic-space point spaces

Zariski locally quasi-separated algebraic spaces and decent algebraic spaces
have sober spaces of points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The point space of a Zariski locally quasi-separated algebraic space is sober. -/
theorem points_sober {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsZariskiLocallyQuasiSeparated X] :
    T0Space (Points X) ∧ QuasiSober (Points X) := by
  sorry

namespace IsZariskiLocallyQuasiSeparated

/-- The point space of a Zariski locally quasi-separated algebraic space is Kolmogorov. -/
instance instT0SpacePoints {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsZariskiLocallyQuasiSeparated X] : T0Space (Points X) := by
  sorry

/-- The point space of a Zariski locally quasi-separated algebraic space is quasi-sober. -/
instance instQuasiSoberPoints {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsZariskiLocallyQuasiSeparated X] : QuasiSober (Points X) := by
  sorry

/-- Every irreducible closed subset of the point space has a unique generic point. -/
theorem existsUnique_isGenericPoint {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsZariskiLocallyQuasiSeparated X] {T : Set (Points X)}
    (hT_irred : IsIrreducible T) (hT_closed : IsClosed T) :
    ∃! x : Points X, IsGenericPoint x T := by
  sorry

end IsZariskiLocallyQuasiSeparated

/-- The point space of a decent algebraic space is sober. -/
@[stacks 03K6]
theorem points_sober_of_isDecent {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X] :
    T0Space (Points X) ∧ QuasiSober (Points X) :=
  sorry

/-- The space of points of a decent algebraic space is quasi-sober. -/
instance instQuasiSoberPoints {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X] :
    QuasiSober (Points X) :=
  (points_sober_of_isDecent X).2

/-- Every irreducible closed subset of the point space of a decent algebraic space
has a unique generic point. -/
theorem existsUnique_isGenericPoint_of_isDecent {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] {T : Set (Points X)} (hT_irred : IsIrreducible T)
    (hT_closed : IsClosed T) :
    ∃! x : Points X, IsGenericPoint x T :=
  sober_iff_forall_irreducibleCloseds_existsUnique_genericPoint.mp
    (points_sober_of_isDecent X)
    (TopologicalSpace.IrreducibleCloseds.mk T hT_irred hT_closed)

/-- The point space of the source of a quasi-separated morphism to a quasi-separated
algebraic space is sober. -/
theorem points_sober_of_quasiSeparated {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [IsQuasiSeparated B] (f : X ⟶ B) [QuasiSeparated f] :
    T0Space (Points X) ∧ QuasiSober (Points X) :=
  sorry

/-- Every irreducible closed subset of the point space of the source of a quasi-separated
morphism to a quasi-separated algebraic space has a unique generic point. -/
theorem existsUnique_isGenericPoint_of_quasiSeparated {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [IsQuasiSeparated B] (f : X ⟶ B) [QuasiSeparated f]
    {T : Set (Points X)} (hT_irred : IsIrreducible T) (hT_closed : IsClosed T) :
    ∃! x : Points X, IsGenericPoint x T :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
