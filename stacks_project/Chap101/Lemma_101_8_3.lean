/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Lemma_101_8_3_Topology
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

/- Lemma 101.8.3 (1): if an algebraic stack `X` over a scheme `S` is locally Noetherian,
then `|X|` is a locally Noetherian topological space. -/
@[stacks 0DQI] #check
  (AlgebraicGeometry.AlgebraicStack.IsLocallyNoetherian.locallyNoetherianSpace :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
      [AlgebraicStack.IsLocallyNoetherian X]
      (τ : TopologicalSpace (AlgebraicStack.Points X))
      (_ : AlgebraicStack.IsPointsTopology X τ),
      @TopologicalSpace.LocallyNoetherianSpace (AlgebraicStack.Points X) τ)

/- Lemma 101.8.3 (2): if an algebraic stack `X` over a scheme `S` is quasi-compact and
locally Noetherian, then `|X|` is a Noetherian topological space. -/
@[stacks 0DQI] #check
  (AlgebraicGeometry.AlgebraicStack.IsLocallyNoetherian.noetherianSpace :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
      [AlgebraicStack.IsQuasiCompact X] [AlgebraicStack.IsLocallyNoetherian X]
      (τ : TopologicalSpace (AlgebraicStack.Points X))
      (_ : AlgebraicStack.IsPointsTopology X τ),
      @TopologicalSpace.NoetherianSpace (AlgebraicStack.Points X) τ)
