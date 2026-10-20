module

public import ReasLib.Topology.Algebra.Ring.Taut
public import ReasLib.RingTheory.Topology.WeaklyAdmissible
public import ReasLib.RingTheory.Topology.CountablyIndexed

/-!
# Sequential inverse-limit characterization of taut homomorphisms

For a continuous homomorphism of countably indexed weakly admissible rings and
a nested fundamental sequence `J` of weak ideals of definition in the source,
the canonical stages are `B ⧸ (Ideal.map φ (J n)).closure`. The vertical maps
are induced by `φ`, and the transitions are canonical quotient factor maps.
The successive-quotient ideal equality specifies reduction from one stage to
the preceding stage. Completeness and separatedness of `B`, together with the
neighborhood-basis condition, recover `B` as their topological inverse limit.
-/

@[expose] public section

open scoped Topology
open TopologicalRing
open TopologicalRing.Ideal

universe u

namespace RingHom

variable {A B : Type u}
variable [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
variable [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]

/-- The closures of the extensions of `J n` are open, satisfy the
successive-quotient ideal equality, and form a neighborhood basis at zero.
For a continuous `φ` and a nested fundamental sequence of weak ideals of
definition `J`, this describes the canonical quotient stages
`B ⧸ (Ideal.map φ (J n)).closure`, with vertical maps induced by `φ` and
transitions given by `Ideal.Quotient.factor`. Completeness and separatedness
of `B` then identify it with the topological inverse limit of these stages. -/
def IsTautInverseLimit (φ : A →+* B) (J : ℕ → Ideal A) : Prop :=
  (∀ n, IsOpen ((Ideal.map φ (J n)).closure : Set B)) ∧
    (∀ n,
        (Ideal.map φ (J n)).closure =
          Ideal.map φ (J n) ⊔ (Ideal.map φ (J (n + 1))).closure) ∧
      (nhds (0 : B)).HasBasis (fun _ : ℕ ↦ True)
        (fun n ↦ ((Ideal.map φ (J n)).closure : Set B))

/-- The sequential inverse-limit criterion is equivalent to openness of the
closures, the successive-quotient ideal equality, and the neighborhood-basis
condition. -/
theorem isTautInverseLimit_iff (φ : A →+* B) (J : ℕ → Ideal A) :
    φ.IsTautInverseLimit J ↔
      (∀ n, IsOpen ((Ideal.map φ (J n)).closure : Set B)) ∧
        (∀ n,
            (Ideal.map φ (J n)).closure =
              Ideal.map φ (J n) ⊔ (Ideal.map φ (J (n + 1))).closure) ∧
          (nhds (0 : B)).HasBasis (fun _ : ℕ ↦ True)
            (fun n ↦ ((Ideal.map φ (J n)).closure : Set B)) :=
  Iff.rfl

namespace IsTautInverseLimit

/-- The sequential inverse-limit criterion implies openness of the closures,
the successive-quotient ideal equality, and the neighborhood-basis condition. -/
theorem spec {φ : A →+* B} {J : ℕ → Ideal A} (h : φ.IsTautInverseLimit J) :
    (∀ n, IsOpen ((Ideal.map φ (J n)).closure : Set B)) ∧
      (∀ n,
          (Ideal.map φ (J n)).closure =
            Ideal.map φ (J n) ⊔ (Ideal.map φ (J (n + 1))).closure) ∧
        (nhds (0 : B)).HasBasis (fun _ : ℕ ↦ True)
          (fun n ↦ ((Ideal.map φ (J n)).closure : Set B)) :=
  h

end IsTautInverseLimit

/-- A continuous homomorphism of countably indexed weakly admissible rings is
taut if and only if a nested fundamental sequence of weak ideals of definition
in its source satisfies the sequential inverse-limit criterion. The canonical
stages are `B ⧸ (Ideal.map φ (J n)).closure`, with maps induced by `φ` and
canonical quotient transitions. The ideal equality gives the successive
quotients, while completeness, separatedness, and the neighborhood basis
recover `B` as the topological inverse limit. -/
theorem isTaut_iff_isTautInverseLimit {φ : A →+* B} (hφ : Continuous φ)
    {J : ℕ → Ideal A} (hJ : ∀ n, IsWeakIdealOfDefinition (J n))
    (hJnested : ∀ n, J (n + 1) ≤ J n)
    (hJbasis : (nhds (0 : A)).HasBasis (fun _ : ℕ ↦ True) (fun n ↦ (J n : Set A))) :
    φ.IsTaut ↔ φ.IsTautInverseLimit J :=
  sorry

end RingHom
