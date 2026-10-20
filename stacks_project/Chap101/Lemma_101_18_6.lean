module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FiniteTypePoints.Topology
import StacksCheckRecall

/-!
# Finite-type points meet every nonempty locally closed subset

Every nonempty locally closed subset of the points of an algebraic stack meets
the finite-type points, and the finite-type points of a closed subset are dense
in that subset.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.18.6: Every nonempty locally closed subset of the points of an
algebraic stack meets the finite-type points, which are dense in every closed
subset. -/
@[stacks 06G2] #check
  (AlgebraicGeometry.AlgebraicStack.nonempty_inter_finiteTypePoints :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
      {T : Set (Points X)} (hne : T.Nonempty) (hT : IsLocallyClosed T),
      (T ∩ finiteTypePoints X).Nonempty)

#check
  (AlgebraicGeometry.AlgebraicStack.dense_finiteTypePoints_in_closed_subset :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
      {T : Set (Points X)} (hT : IsClosed T),
      Dense (setOf fun (x : T) ↦ (x : Points X) ∈ finiteTypePoints X))

#check
  (AlgebraicGeometry.AlgebraicStack.closure_inter_finiteTypePoints :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
      {T : Set (Points X)} (hT : IsClosed T),
      closure (T ∩ finiteTypePoints X) = T)

end AlgebraicGeometry.AlgebraicStack
