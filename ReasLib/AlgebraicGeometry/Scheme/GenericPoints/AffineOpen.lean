module

public import Mathlib.AlgebraicGeometry.Limits

@[expose] public section

open TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [QuasiSeparatedSpace X.carrier]
variable {n : ℕ}

/-- Pairwise distinct irreducible components of a quasi-separated scheme, equipped with chosen
generic points, have pairwise disjoint affine open neighborhoods of those points. -/
theorem exists_pairwiseDisjoint_affineOpenNeighborhoods_of_genericPoints
    (Z : Fin n → irreducibleComponents X) (η : Fin n → X)
    (hpairwise : Pairwise fun i j ↦ Z i ≠ Z j)
    (hη : ∀ i, IsGenericPoint (η i) (Z i : Set X)) :
    ∃ U : Fin n → X.affineOpens,
      (∀ i, η i ∈ ((U i : X.Opens) : Set X)) ∧
        Pairwise (fun i j ↦ Disjoint (U i : X.Opens) (U j : X.Opens)) := sorry

/-- Finitely many chosen generic points of pairwise distinct irreducible components of a
quasi-separated scheme lie in a common affine open. -/
theorem exists_affineOpen_containing_genericPoints
    (Z : Fin n → irreducibleComponents X) (η : Fin n → X)
    (hpairwise : Pairwise fun i j ↦ Z i ≠ Z j)
    (hη : ∀ i, IsGenericPoint (η i) (Z i : Set X)) :
    ∃ U : X.affineOpens, ∀ i, η i ∈ ((U : X.Opens) : Set X) := sorry

/-- An arbitrary point and finitely many chosen generic points of pairwise distinct irreducible
components of a quasi-separated scheme lie in a common affine open. -/
theorem exists_affineOpen_containing_point_and_genericPoints
    (x : X) (Z : Fin n → irreducibleComponents X) (η : Fin n → X)
    (hpairwise : Pairwise fun i j ↦ Z i ≠ Z j)
    (hη : ∀ i, IsGenericPoint (η i) (Z i : Set X)) :
    ∃ U : X.affineOpens,
      x ∈ ((U : X.Opens) : Set X) ∧ ∀ i, η i ∈ ((U : X.Opens) : Set X) := sorry

end AlgebraicGeometry.Scheme
