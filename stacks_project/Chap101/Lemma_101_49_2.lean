/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sober
public import stacks_project.Chap101.Definition_101_8_1_Noetherian
public import stacks_project.Chap101.Definition_101_13_2_Closed
public import stacks_project.Chap101.Definition_101_50_1_Decent
public import stacks_project.Chap101.Lemma_101_8_3_Topology
import StacksCheckRecall

/-!
# Sober points of decent locally Noetherian algebraic stacks

The points space of a decent locally Noetherian algebraic stack is sober in the
sense of Topology, Definition 5.8.6, and locally Noetherian.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicStack

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsDecent

/-- Lemma 101.49.2 (1): Let `X` be a decent, locally Noetherian algebraic stack.
Then `|X|` is a sober topological space, i.e. `@T0Space (Points X) τ` and
`@QuasiSober (Points X) τ` for every canonical `IsPointsTopology`. -/
@[stacks 0GW8]
theorem sober {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsDecent X] [IsLocallyNoetherian X] (τ : TopologicalSpace (Points X))
    (hτ : IsPointsTopology X τ) :
    @T0Space (Points X) τ ∧ @QuasiSober (Points X) τ :=
  sorry

/-- Every irreducible closed subset of the points space of a decent locally
Noetherian algebraic stack has a unique generic point. -/
theorem existsUnique_isGenericPoint {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsDecent X] [IsLocallyNoetherian X]
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ)
    {T : Set (Points X)} (hT_irred : @IsIrreducible (Points X) τ T)
    (hT_closed : @IsClosed (Points X) τ T) :
    ∃! x, @IsGenericPoint (Points X) τ x T :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsDecent

/- Lemma 101.49.2 (2): if an algebraic stack `X` is locally Noetherian, then
`|X|` is a locally Noetherian topological space. -/
@[stacks 0GW8] #check
  (IsLocallyNoetherian.locallyNoetherianSpace :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
      [IsLocallyNoetherian X] (τ : TopologicalSpace (Points X))
      (_ : IsPointsTopology X τ),
      @TopologicalSpace.LocallyNoetherianSpace (Points X) τ)
