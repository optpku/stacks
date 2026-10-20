module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Sober
import StacksCheckRecall

/-!
# Sober points of decent algebraic stacks with quasi-compact inertia

The points space of a decent algebraic stack whose inertia morphism is
quasi-compact is sober in the sense of Topology, Definition 5.8.6.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicStack
open FiberedCategoryOver.Groupoids.Inertia (forget)
open scoped Bicategory

universe u

/- Proposition 101.49.3: The point space of a decent algebraic stack with
quasi-compact inertia projection is sober. -/
@[stacks 0GW9] #check
  (AlgebraicGeometry.AlgebraicStack.IsDecent.sober_of_quasiCompact_inertia :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] [IsDecent X]
      [QuasiCompact (forget.{u + 1, u, u, u + 1} X)],
      T0Space (Points X) ∧ QuasiSober (Points X))

#check
  (AlgebraicGeometry.AlgebraicStack.IsDecent.existsUnique_isGenericPoint_of_quasiCompact_inertia :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] [IsDecent X]
      [QuasiCompact (forget.{u + 1, u, u, u + 1} X)] {T : Set (Points X)},
      IsIrreducible T → IsClosed T → ∃! x : Points X, IsGenericPoint x T)
