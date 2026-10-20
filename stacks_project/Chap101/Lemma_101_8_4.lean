/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.QuasiSober
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

/- Lemma 101.8.4: if an algebraic stack `X` over a scheme `S` is locally Noetherian,
then `|X|` is quasi-sober in the sense of Topology, Definition 5.8.6. -/
@[stacks 0GVX] #check
  (AlgebraicGeometry.AlgebraicStack.IsLocallyNoetherian.quasiSober :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
      [AlgebraicStack.IsLocallyNoetherian X]
      (τ : TopologicalSpace (AlgebraicStack.Points X))
      (_ : AlgebraicStack.IsPointsTopology X τ),
      @QuasiSober (AlgebraicStack.Points X) τ)
