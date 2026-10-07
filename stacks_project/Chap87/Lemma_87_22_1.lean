module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_5_1_Taut
public import stacks_project.Chap87.Situation_87_21_2_MorphismProperty

/-!
# Sequential characterization of taut arrows of WAdm^count

A continuous arrow of countably indexed weakly admissible rings is taut if and
only if it admits a sequential inverse-limit presentation along a nested
countable fundamental system of weak ideals of definition, and this property
is local in the sense of Situation 87.21.2.
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

/-- Sequential inverse-limit form of tautness along a nested countable system
`J` of ideals of the source: the closures of `Ideal.map φ (J n)` are open in
the target, the successive quotient stages
`B ⧸ (Ideal.map φ (J n)).closure` satisfy
`(Ideal.map φ (J n)).closure =
Ideal.map φ (J n) ⊔ (Ideal.map φ (J (n + 1))).closure`
(equivalently
`(B ⧸ (Ideal.map φ (J (n + 1))).closure) ⧸ J n · _ =
B ⧸ (Ideal.map φ (J n)).closure`,
with vertical maps `A ⧸ J n ⟶ B ⧸ (Ideal.map φ (J n)).closure` and
transitions `Ideal.Quotient.factor`), and those closures form a neighborhood
basis of `0` in `B`, equivalently
`B = lim (B ⧸ (Ideal.map φ (J n)).closure)` as topological rings. -/
def IsTautInverseLimit (φ : A →+* B) (J : ℕ → Ideal A) : Prop :=
  (∀ n, IsOpen ((Ideal.map φ (J n)).closure : Set B)) ∧
    (∀ n,
        (Ideal.map φ (J n)).closure =
          Ideal.map φ (J n) ⊔ (Ideal.map φ (J (n + 1))).closure) ∧
      (nhds (0 : B)).HasBasis (fun _ : ℕ ↦ True)
        (fun n ↦ ((Ideal.map φ (J n)).closure : Set B))

/-- Unfold sequential tautness as openness of closures, successive-quotient
ideal equality, and a neighborhood basis of those closures. -/
theorem isTautInverseLimit_iff (φ : A →+* B) (J : ℕ → Ideal A) :
    φ.IsTautInverseLimit J ↔
      (∀ n, IsOpen ((Ideal.map φ (J n)).closure : Set B)) ∧
        (∀ n,
            (Ideal.map φ (J n)).closure =
              Ideal.map φ (J n) ⊔ (Ideal.map φ (J (n + 1))).closure) ∧
          (nhds (0 : B)).HasBasis (fun _ : ℕ ↦ True)
            (fun n ↦ ((Ideal.map φ (J n)).closure : Set B)) :=
  sorry

namespace IsTautInverseLimit

/-- Sequential tautness projects to openness of closures, successive-quotient
ideal equality, and a neighborhood basis of those closures. -/
theorem spec {φ : A →+* B} {J : ℕ → Ideal A} (h : φ.IsTautInverseLimit J) :
    (∀ n, IsOpen ((Ideal.map φ (J n)).closure : Set B)) ∧
      (∀ n,
          (Ideal.map φ (J n)).closure =
            Ideal.map φ (J n) ⊔ (Ideal.map φ (J (n + 1))).closure) ∧
        (nhds (0 : B)).HasBasis (fun _ : ℕ ↦ True)
          (fun n ↦ ((Ideal.map φ (J n)).closure : Set B)) :=
  sorry

end IsTautInverseLimit

/-- Lemma 87.22.1 (1): Let `φ : A →+* B` be a continuous arrow of
`WAdm^count`. Then `φ` is taut if and only if, for a nested countable
fundamental system `J` of weak ideals of definition of `A`, there is a
commutative diagram of successive quotients
`A ⧸ J n ⟶ B ⧸ (Ideal.map φ (J n)).closure` with transitions
`Ideal.Quotient.factor` such that
`(Ideal.map φ (J n)).closure =
Ideal.map φ (J n) ⊔ (Ideal.map φ (J (n + 1))).closure`
(i.e. the stages `B ⧸ (Ideal.map φ (J n)).closure` satisfy
`(B ⧸ (Ideal.map φ (J (n + 1))).closure) ⧸ J n · _ =
B ⧸ (Ideal.map φ (J n)).closure`) and
`B = lim (B ⧸ (Ideal.map φ (J n)).closure)` as topological rings,
equivalently `(nhds (0 : B)).HasBasis` of those closures. -/
@[stacks 0ANJ]
theorem isTaut_iff_isTautInverseLimit {φ : A →+* B} (hφ : Continuous φ)
    {J : ℕ → Ideal A} (hJ : ∀ n, IsWeakIdealOfDefinition (J n))
    (hJnested : ∀ n, J (n + 1) ≤ J n)
    (hJbasis : (nhds (0 : A)).HasBasis (fun _ : ℕ ↦ True) (fun n ↦ (J n : Set A))) :
    φ.IsTaut ↔ φ.IsTautInverseLimit J :=
  sorry

end RingHom

namespace TopologicalRing

/-- Lemma 87.22.1 (2): Tautness of arrows of `WAdm^count` is a local
property in the sense of Situation 87.21.2, i.e. it satisfies axioms (1),
(2), and (3). -/
@[stacks 0ANJ]
theorem isLocalMorphismProperty_isTaut :
    IsLocalMorphismProperty
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
        [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
        (φ : B →+* A) ↦ φ.IsTaut :=
  sorry

end TopologicalRing
