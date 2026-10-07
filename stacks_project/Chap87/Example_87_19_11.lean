module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_19_8
public import stacks_project.Chap87.Lemma_87_19_13_Functor

/-!
# Example 87.19.11

If `B` is weakly admissible and `A` is a `B`-algebra with no topology, the
weak-ideal completion `weakIdealCompletion B A` is weakly admissible, the
algebra map `B → (A)^∧` is taut, and `Spf((A)^∧) ⟶ Spf(B)` is representable
by algebraic spaces as in Lemma 87.19.8.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalRing
open AlgebraicGeometry.AffineFormalAlgebraicSpace AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace TopologicalRing.weakIdealCompletion

variable {B A : Type u} [CommRing B] [TopologicalSpace B] [CommRing A] [Algebra B A]

/-- The stage projection `(A)^∧ → A ⧸ J A` from `weakIdealCompletion B A` is
surjective. -/
theorem eval_surjective {J : Ideal B} (hJ : Ideal.IsWeakIdealOfDefinition J) :
    Function.Surjective (eval B A hJ) :=
  sorry

variable [IsWeaklyAdmissibleRing B]

/-- Example 87.19.11 (1): the kernel of the stage projection
`eval B A hJ : weakIdealCompletion B A →+* A ⧸ J A` equals the closure of
`J.map (algebraMap B (weakIdealCompletion B A))`. -/
@[stacks 0AN6]
theorem eval_ker_eq_closure {J : Ideal B} (hJ : Ideal.IsWeakIdealOfDefinition J) :
    RingHom.ker (eval B A hJ) =
      (J.map (algebraMap B (weakIdealCompletion B A))).closure :=
  sorry

/-- Membership in `RingHom.ker (eval B A hJ)` is membership in the closure of
the extended ideal `J (A)^∧`. -/
theorem mem_eval_ker {J : Ideal B} (hJ : Ideal.IsWeakIdealOfDefinition J)
    {x : weakIdealCompletion B A} :
    x ∈ RingHom.ker (eval B A hJ) ↔
      x ∈ (J.map (algebraMap B (weakIdealCompletion B A))).closure :=
  sorry

/-- Example 87.19.11 (2): the kernel of `eval B A hJ` is a weak ideal of
definition of `weakIdealCompletion B A`. Weak admissibility of the completion
is `instIsWeaklyAdmissibleRing_weakIdealCompletion`. -/
@[stacks 0AN6]
theorem isWeakIdealOfDefinition_eval_ker {J : Ideal B}
    (hJ : Ideal.IsWeakIdealOfDefinition J) :
    Ideal.IsWeakIdealOfDefinition (RingHom.ker (eval B A hJ)) :=
  sorry

/-- The kernel of each stage projection `(A)^∧ → A ⧸ J A` is open. -/
theorem isOpen_eval_ker {J : Ideal B} (hJ : Ideal.IsWeakIdealOfDefinition J) :
    IsOpen (RingHom.ker (eval B A hJ) : Set (weakIdealCompletion B A)) :=
  sorry

/-- Example 87.19.11 (3): the algebra map
`φ = algebraMap B (weakIdealCompletion B A)` is a taut map of weakly
admissible topological rings. -/
@[stacks 0AN6]
theorem isTaut_algebraMap : (algebraMap B (weakIdealCompletion B A)).IsTaut :=
  sorry

end TopologicalRing.weakIdealCompletion

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

variable {S : Scheme.{u}} {B : Type u} [CommRing B] [TopologicalSpace B]
  [TopologicalRing.IsWeaklyAdmissibleRing B] (hB : Spec (.of B) ⟶ S)
  [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
  (A : Type u) [CommRing A] [Algebra B A]

/-- Example 87.19.11 (4): `Spf(weakIdealCompletion B A) ⟶ Spf(B)` is
representable by algebraic spaces, the taut special case of Lemma 87.19.8. -/
@[stacks 0AN6]
theorem representableByAlgebraicSpaces_spfMap_weakIdealCompletion :
    AlgebraicSpace.representableByAlgebraicSpaces
      ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
        (spfMap_weakIdealCompletion hB A)) :=
  sorry

/-- `Spf(weakIdealCompletion B A) ⟶ Spf(B)` is representable by schemes. -/
theorem relativelyRepresentable_spfMap_weakIdealCompletion :
    yoneda.relativelyRepresentable
      ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
        (spfMap_weakIdealCompletion hB A)) :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
