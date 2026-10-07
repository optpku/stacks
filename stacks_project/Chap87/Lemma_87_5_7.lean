module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Order.Filter.CountablyGenerated
public import stacks_project.Chap87.Definition_87_5_1_Taut

/-!
# Lemma 87.5.7

A continuous taut homomorphism of linearly topologized rings transfers a
countable fundamental system of open ideals from the source to the target.
-/

@[expose] public section

universe u v

open scoped Topology

namespace RingHom.IsTaut

variable {A : Type u} {B : Type v}
variable [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
variable [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]

/-- Lemma 87.5.7: Let `φ : A →+* B` be a continuous homomorphism of linearly
topologized rings. If `φ` is taut and `A` has a countable fundamental system of
open ideals, then `B` has a countable fundamental system of open ideals. -/
@[stacks 0GX6]
theorem isCountablyGenerated_nhds {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut)
    [(nhds (0 : A)).IsCountablyGenerated] :
    (nhds (0 : B)).IsCountablyGenerated :=
  sorry

/-- If `I n` is a countable fundamental system of open ideals of `A` and `φ` is
taut, then the closures of `Ideal.map φ (I n)` form a countable fundamental
system of neighborhoods of `0` in `B`. -/
theorem hasBasis_closure_map {I : ℕ → Ideal A} (hIopen : ∀ n, IsOpen (I n : Set A))
    (hI : (nhds (0 : A)).HasBasis (fun _ : ℕ ↦ True) (fun n ↦ (I n : Set A)))
    {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut) :
    (nhds (0 : B)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ ((Ideal.map φ (I n)).closure : Set B)) :=
  sorry

end RingHom.IsTaut
