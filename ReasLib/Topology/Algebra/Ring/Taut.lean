module

public import Mathlib.Order.Filter.CountablyGenerated
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Ring.Ideal

/-!
# Taut homomorphisms of linearly topologized rings

A continuous homomorphism of linearly topologized rings is taut when the closures of the
extensions of open ideals of the source form a fundamental system of open ideals of the target.
-/

@[expose] public section

open scoped Topology

universe u v w

namespace RingHom

/-- A homomorphism of linearly topologized rings is taut if the closures of the
extensions of open ideals of the source form a fundamental system of neighborhoods
of `0` in the target. -/
def IsTaut {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    (φ : A →+* B) : Prop :=
  (nhds (0 : B)).HasBasis (fun I : Ideal A ↦ IsOpen (I : Set A))
    (fun I ↦ ((Ideal.map φ I).closure : Set B))

variable {A : Type u} {B : Type v}
variable [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
variable [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
variable {C : Type w}
variable [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]

/-- A homomorphism of linearly topologized rings is taut if and only if, for every
open ideal of the source, the closure of its extension is open in the target, and
these closures are cofinal among open ideals of the target. -/
theorem isTaut_iff (φ : A →+* B) :
    φ.IsTaut ↔
      (∀ I : Ideal A, IsOpen (I : Set A) → IsOpen ((Ideal.map φ I).closure : Set B)) ∧
        ∀ J : Ideal B, IsOpen (J : Set B) →
          ∃ I : Ideal A, IsOpen (I : Set A) ∧ (Ideal.map φ I).closure ≤ J := sorry

namespace IsTaut

/-- If `φ` is taut, then the closure of the extension of every open ideal of the
source is open in the target. -/
theorem isOpen_closure_map {φ : A →+* B} (hφ : φ.IsTaut) {I : Ideal A}
    (hI : IsOpen (I : Set A)) : IsOpen ((Ideal.map φ I).closure : Set B) := sorry

/-- If `φ` is taut, then every open ideal of the target contains the closure of the
extension of some open ideal of the source. -/
theorem exists_closure_map_le {φ : A →+* B} (hφ : φ.IsTaut) {J : Ideal B}
    (hJ : IsOpen (J : Set B)) :
    ∃ I : Ideal A, IsOpen (I : Set A) ∧ (Ideal.map φ I).closure ≤ J := sorry

/-- If a composite of continuous homomorphisms of linearly topologized rings is taut,
then the second homomorphism is taut. -/
theorem of_comp {φ : A →+* B} {ψ : B →+* C} (hφ_cont : Continuous φ)
    (hψ_cont : Continuous ψ) (h : (ψ.comp φ).IsTaut) : ψ.IsTaut := sorry

/-- The composite of two continuous taut homomorphisms of linearly topologized rings
is taut. -/
theorem comp {φ : A →+* B} {ψ : B →+* C} (hφ_cont : Continuous φ)
    (hψ_cont : Continuous ψ) (hφ : φ.IsTaut) (hψ : ψ.IsTaut) :
    (ψ.comp φ).IsTaut := sorry

/-- A continuous taut homomorphism of linearly topologized rings transfers a
countable fundamental system of open ideals from the source to the target. -/
theorem isCountablyGenerated_nhds {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut)
    [(nhds (0 : A)).IsCountablyGenerated] :
    (nhds (0 : B)).IsCountablyGenerated :=
  sorry

end IsTaut

/-- If `I` is a fundamental system of open ideals of `A`, then `φ` is taut if and
only if the closures of the extensions `Ideal.map φ (I i)` are open and form a
fundamental system of neighborhoods of `0` in `B`. -/
theorem isTaut_iff_hasBasis {ι : Type w} {I : ι → Ideal A}
    (hI : (nhds (0 : A)).HasBasis (fun _ ↦ True) (fun i ↦ (I i : Set A)))
    (hIopen : ∀ i, IsOpen (I i : Set A)) (φ : A →+* B) :
    φ.IsTaut ↔
      (∀ i, IsOpen ((Ideal.map φ (I i)).closure : Set B)) ∧
        (nhds (0 : B)).HasBasis (fun _ ↦ True)
          (fun i ↦ ((Ideal.map φ (I i)).closure : Set B)) := sorry

end RingHom
