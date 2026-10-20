module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Order.Filter.CountablyGenerated
public import ReasLib.Topology.Algebra.Ring.Taut
public import ReasLib.Topology.Algebra.Ring.FaithfullyFlatOpenQuotients

/-!
# Countability descent along homomorphisms with faithfully flat open quotients

A countable fundamental system of open ideals descends along a continuous taut
homomorphism of linearly topologized rings with faithfully flat open quotients.
-/

@[expose] public section

universe u v

open scoped Topology

namespace RingHom.FaithfullyFlatOpenQuotients

variable {A : Type u} {B : Type v}
variable [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
variable [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]

/-- For a continuous taut homomorphism of linearly topologized rings with
faithfully flat open quotients, countable generation of the neighborhood filter
of zero in the target implies countable generation in the source. -/
@[stacks 0GXL]
theorem isCountablyGenerated_nhds {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut)
    (hff : φ.FaithfullyFlatOpenQuotients) [(nhds (0 : B)).IsCountablyGenerated] :
    (nhds (0 : A)).IsCountablyGenerated :=
  sorry

/-- For a continuous taut homomorphism of linearly topologized rings with
faithfully flat open quotients, a countable fundamental system of open ideals of
the target implies the existence of a countable fundamental system of open
ideals of the source. -/
theorem exists_hasBasis_open_ideal {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut)
    (hff : φ.FaithfullyFlatOpenQuotients) {J : ℕ → Ideal B}
    (hJopen : ∀ n, IsOpen (J n : Set B))
    (hJ : (nhds (0 : B)).HasBasis (fun _ : ℕ ↦ True) (fun n ↦ (J n : Set B))) :
    ∃ I : ℕ → Ideal A, (∀ n, IsOpen (I n : Set A)) ∧
      (nhds (0 : A)).HasBasis (fun _ : ℕ ↦ True) (fun n ↦ (I n : Set A)) :=
  sorry

end RingHom.FaithfullyFlatOpenQuotients
