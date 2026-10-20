/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Sober
import StacksCheckRecall

/-!
# Sober points of decent locally Noetherian algebraic stacks

The points space of a decent locally Noetherian algebraic stack is sober in the
sense of Topology, Definition 5.8.6, and locally Noetherian.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicStack

universe u

/- Lemma 101.49.2: The points space of a decent locally Noetherian algebraic
stack is sober and locally Noetherian. -/
@[stacks 0GW8] #check
  (AlgebraicGeometry.AlgebraicStack.IsDecent.sober :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
      [IsDecent X] [IsLocallyNoetherian X] (τ : TopologicalSpace (Points X))
      (hτ : IsPointsTopology X τ),
      @T0Space (Points X) τ ∧ @QuasiSober (Points X) τ ∧
        @TopologicalSpace.LocallyNoetherianSpace (Points X) τ)

#check
  (AlgebraicGeometry.AlgebraicStack.IsDecent.existsUnique_isGenericPoint :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
      [IsDecent X] [IsLocallyNoetherian X] {τ : TopologicalSpace (Points X)}
      (hτ : IsPointsTopology X τ) {T : Set (Points X)}
      (hT_irred : @IsIrreducible (Points X) τ T)
      (hT_closed : @IsClosed (Points X) τ T),
      ∃! x, @IsGenericPoint (Points X) τ x T)

/- Local Noetherianity also holds without the decency assumption. -/
#check
  (AlgebraicGeometry.AlgebraicStack.IsLocallyNoetherian.locallyNoetherianSpace :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
      [IsLocallyNoetherian X] (τ : TopologicalSpace (Points X))
      (_ : IsPointsTopology X τ),
      @TopologicalSpace.LocallyNoetherianSpace (Points X) τ)
