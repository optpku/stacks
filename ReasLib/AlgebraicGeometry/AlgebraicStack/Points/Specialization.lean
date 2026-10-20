/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Smooth

/-!
# Lifting specializations through smooth morphisms

Specializations of algebraic-stack points lift through smooth morphisms from
algebraic spaces when the generizing point has a quasi-compact field-valued
representative.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A specialization `x' ⤳ x` lifts through a smooth morphism from an algebraic
space at every point above `x`, provided `x'` has a quasi-compact field-valued
representative. -/
theorem exists_specializes_of_smooth {S : Scheme.{u}} {U : AlgebraicSpace S}
    {X : GroupoidsOver S} [AlgebraicStack X] (f : U.toGroupoids ⟶ X) [Smooth f]
    {x x' : Points X} (hspec : Specializes x' x)
    (h_quasiCompact : existsQuasiCompactFieldValuedPoint X x')
    {u : AlgebraicSpace.Points U} (hu : Points.mapSpace f u = x) :
    ∃ u' : AlgebraicSpace.Points U,
      Specializes u' u ∧ Points.mapSpace f u' = x' := sorry

/-- A specialization `x' ⤳ x` lifts through a smooth morphism from an algebraic
space at every point above `x` when every field-valued representative of `x'`
is quasi-compact. -/
theorem exists_specializes_of_smooth_of_forallFieldValuedPointQuasiCompact
    {S : Scheme.{u}} {U : AlgebraicSpace S} {X : GroupoidsOver S}
    [AlgebraicStack X] (f : U.toGroupoids ⟶ X) [Smooth f] {x x' : Points X}
    (hspec : Specializes x' x)
    (h_quasiCompact : forallFieldValuedPointQuasiCompact X x')
    {u : AlgebraicSpace.Points U} (hu : Points.mapSpace f u = x) :
    ∃ u' : AlgebraicSpace.Points U,
      Specializes u' u ∧ Points.mapSpace f u' = x' := sorry

end AlgebraicGeometry.AlgebraicStack
