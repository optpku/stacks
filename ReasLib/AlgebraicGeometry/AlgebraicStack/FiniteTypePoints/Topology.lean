/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FiniteTypePoints
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Topology

/-!
# Topology of finite-type points of algebraic stacks

Finite-type points meet every nonempty locally closed subset and are dense in
every closed subspace of an algebraic stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Every nonempty locally closed subset of the points of an algebraic stack
contains a finite-type point. -/
theorem nonempty_inter_finiteTypePoints {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] {T : Set (Points X)} (hne : T.Nonempty)
    (hT : IsLocallyClosed T) :
    (T ∩ finiteTypePoints X).Nonempty :=
  sorry

/-- The finite-type points of an algebraic stack lying in a closed subset are
dense in that subset. -/
theorem dense_finiteTypePoints_in_closed_subset {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] {T : Set (Points X)}
    (hT : IsClosed T) :
    Dense (setOf fun (x : T) ↦ (x : Points X) ∈ finiteTypePoints X) :=
  sorry

/-- The closure of the finite-type points of an algebraic stack inside a closed
subset `T` is `T`. -/
theorem closure_inter_finiteTypePoints {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] {T : Set (Points X)} (hT : IsClosed T) :
    closure (T ∩ finiteTypePoints X) = T :=
  sorry

end AlgebraicGeometry.AlgebraicStack
