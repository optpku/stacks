/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.AffineOpen
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 28.29.1: pairwise distinct irreducible components of a quasi-separated scheme,
equipped with chosen generic points, have pairwise disjoint affine open neighborhoods. -/
@[stacks 01ZV] #check
  (AlgebraicGeometry.Scheme.exists_pairwiseDisjoint_affineOpenNeighborhoods_of_genericPoints :
    ∀ {X : Scheme.{u}} [QuasiSeparatedSpace X.carrier] {n : ℕ}
      (Z : Fin n → irreducibleComponents X) (η : Fin n → X),
      Pairwise (fun i j ↦ Z i ≠ Z j) →
        (∀ i, IsGenericPoint (η i) (Z i : Set X)) →
          ∃ U : Fin n → X.affineOpens,
            (∀ i, η i ∈ ((U i : X.Opens) : Set X)) ∧
              Pairwise (fun i j ↦ Disjoint (U i : X.Opens) (U j : X.Opens)))

#check (AlgebraicGeometry.Scheme.exists_affineOpen_containing_genericPoints :
  ∀ {X : Scheme.{u}} [QuasiSeparatedSpace X.carrier] {n : ℕ}
    (Z : Fin n → irreducibleComponents X) (η : Fin n → X),
    Pairwise (fun i j ↦ Z i ≠ Z j) →
      (∀ i, IsGenericPoint (η i) (Z i : Set X)) →
        ∃ U : X.affineOpens, ∀ i, η i ∈ ((U : X.Opens) : Set X))
