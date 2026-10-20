/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sober
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Kolmogorov
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Inertia
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Kolmogorov
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.QuasiSober
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Noetherian

/-!
# Sobriety of points of decent algebraic stacks

The canonical point space of a decent algebraic stack is sober if the stack is
locally Noetherian or its inertia projection is quasi-compact. In the locally
Noetherian case, the point space is also locally Noetherian.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicStack
open FiberedCategoryOver.Groupoids.Inertia (forget)
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsDecent

/-- Every canonical topology on the points of a decent locally Noetherian
algebraic stack is sober and locally Noetherian. -/
@[stacks 0GW8]
theorem sober {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsDecent X] [IsLocallyNoetherian X] (τ : TopologicalSpace (Points X))
    (hτ : IsPointsTopology X τ) :
    @T0Space (Points X) τ ∧ @QuasiSober (Points X) τ ∧
      @TopologicalSpace.LocallyNoetherianSpace (Points X) τ :=
  ⟨IsDecent.t0Space X τ hτ, IsLocallyNoetherian.quasiSober X τ hτ,
    IsLocallyNoetherian.locallyNoetherianSpace X τ hτ⟩

/-- Every irreducible closed subset of the points space of a decent locally
Noetherian algebraic stack has a unique generic point. -/
theorem existsUnique_isGenericPoint {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsDecent X] [IsLocallyNoetherian X]
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ)
    {T : Set (Points X)} (hT_irred : @IsIrreducible (Points X) τ T)
    (hT_closed : @IsClosed (Points X) τ T) :
    ∃! x, @IsGenericPoint (Points X) τ x T :=
  sorry

/-- The canonical point space of a decent algebraic stack whose inertia
projection is quasi-compact is sober. -/
@[stacks 0GW9]
theorem sober_of_quasiCompact_inertia {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsDecent X]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)] :
    T0Space (Points X) ∧ QuasiSober (Points X) :=
  sorry

/-- The canonical point space of a decent algebraic stack with quasi-compact
inertia projection is quasi-sober. -/
instance instQuasiSoberPoints {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsDecent X]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)] :
    QuasiSober (Points X) :=
  (sober_of_quasiCompact_inertia X).2

/-- Every irreducible closed subset of the canonical point space of a decent
algebraic stack with quasi-compact inertia projection has a unique generic point. -/
theorem existsUnique_isGenericPoint_of_quasiCompact_inertia
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] [IsDecent X]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)]
    {T : Set (Points X)} (hT_irred : IsIrreducible T) (hT_closed : IsClosed T) :
    ∃! x : Points X, IsGenericPoint x T :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsDecent
