/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Order.Filter.CountablyGenerated
public import stacks_project.Chap87.Definition_87_5_1_Taut
public import stacks_project.Chap87.Lemma_87_8_3_OpenQuotient

/-!
# Lemma 87.8.1

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

/-- Lemma 87.8.1: In the situation of a continuous taut homomorphism `φ : A →+* B`
of linearly topologized rings with `φ.FaithfullyFlatOpenQuotients`, if `B` has a
countable fundamental system of open ideals, then `A` has a countable fundamental
system of open ideals. -/
@[stacks 0GXL]
theorem isCountablyGenerated_nhds {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut)
    (hff : φ.FaithfullyFlatOpenQuotients) [(nhds (0 : B)).IsCountablyGenerated] :
    (nhds (0 : A)).IsCountablyGenerated :=
  sorry

/-- If `J n` is a countable fundamental system of open ideals of `B`, then there
exists a countable fundamental system of open ideals of `A`. -/
theorem exists_hasBasis_open_ideal {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut)
    (hff : φ.FaithfullyFlatOpenQuotients) {J : ℕ → Ideal B}
    (hJopen : ∀ n, IsOpen (J n : Set B))
    (hJ : (nhds (0 : B)).HasBasis (fun _ : ℕ ↦ True) (fun n ↦ (J n : Set B))) :
    ∃ I : ℕ → Ideal A, (∀ n, IsOpen (I n : Set A)) ∧
      (nhds (0 : A)).HasBasis (fun _ : ℕ ↦ True) (fun n ↦ (I n : Set A)) :=
  sorry

end RingHom.FaithfullyFlatOpenQuotients
