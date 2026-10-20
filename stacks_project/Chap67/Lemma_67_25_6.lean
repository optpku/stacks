module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteTypePoints.Topology
import StacksCheckRecall

/-!
# Finite-type points meet every nonempty locally closed subset

Every nonempty locally closed subset of the points of an algebraic space meets
the finite-type points, and the finite-type points of a closed subset are dense
in that subset.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.25.6: Every nonempty locally closed subset of the points of an
algebraic space over a scheme contains a finite-type point. The finite-type
points lying in any closed subset are dense in that subset. -/
@[stacks 06EK] #check (AlgebraicGeometry.AlgebraicSpace.nonempty_inter_finiteTypePoints :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) {T : Set (Points X)},
    T.Nonempty → IsLocallyClosed T → (T ∩ finiteTypePoints X).Nonempty)

@[stacks 06EK] #check (AlgebraicGeometry.AlgebraicSpace.dense_finiteTypePoints_in_closed_subset :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) {T : Set (Points X)},
    IsClosed T → Dense (setOf fun (x : T) ↦ (x : Points X) ∈ finiteTypePoints X))

#check (AlgebraicGeometry.AlgebraicSpace.closure_inter_finiteTypePoints :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) {T : Set (Points X)},
    IsClosed T → closure (T ∩ finiteTypePoints X) = T)

end AlgebraicGeometry.AlgebraicSpace
