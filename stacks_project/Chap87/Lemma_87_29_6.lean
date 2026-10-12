/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_5_1_Taut
public import stacks_project.Chap87.Definition_87_29_1_TopologicallyOfFiniteType
public import stacks_project.Chap87.Lemma_87_29_6_RestrictedPowerSeries
public import stacks_project.Chap87.Lemma_87_29_6_WeakIdealQuotients
public import stacks_project.Chap87.Situation_87_21_2_MorphismProperty

/-!
# Taut topologically finite type arrows of WAdm^count

A continuous arrow of countably indexed weakly admissible rings is taut and
topologically of finite type if and only if its weak-ideal reductions are of
finite type, equivalently if the target is a closed quotient of a finite-variable
restricted power series algebra, and this property is local in the sense of
Situation 87.21.2.
-/

@[expose] public section

open TopologicalRing
open TopologicalRing.Ideal

universe u

namespace RingHom

variable {A B : Type u}
variable [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
variable [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]

/-- Lemma 87.29.6 (1): Let `φ : B →+* A` be a continuous arrow of `WAdm^count`.
The following are equivalent: (a) `φ` is taut and `φ.closureQuotientMap J` is of
finite type for every weak ideal of definition `J` of `B`; (b) `φ` is taut and
`φ.closureQuotientMap (J i)` is of finite type along some cofinal system of weak
ideals of definition of `B`; (c) `φ` is taut and `A` is topologically of finite
type over `B`; (d) `A` is isomorphic as a topological `B`-algebra to a quotient of
`RestrictedPowerSeries (Fin n) B` by a closed ideal. -/
@[stacks 0ANU]
theorem taut_topologicallyOfFiniteType_tfae {φ : B →+* A} (hφ : Continuous φ) :
    List.TFAE
      [φ.IsTaut ∧ φ.IsFiniteTypeOnWeakIdealQuotients,
        φ.IsTaut ∧ φ.IsFiniteTypeOnCofinalWeakIdealQuotients,
        φ.IsTaut ∧ φ.TopologicallyOfFiniteType,
        φ.IsClosedQuotientOfRestrictedPowerSeries] :=
  sorry

/-- Tautness together with finite type on every weak-ideal quotient is equivalent
to tautness together with topological finite type. -/
theorem isTaut_and_isFiniteTypeOnWeakIdealQuotients_iff {φ : B →+* A}
    (hφ : Continuous φ) :
    (φ.IsTaut ∧ φ.IsFiniteTypeOnWeakIdealQuotients) ↔
      φ.IsTaut ∧ φ.TopologicallyOfFiniteType :=
  sorry

/-- Tautness together with finite type along a cofinal weak-ideal system is
equivalent to tautness together with topological finite type. -/
theorem isTaut_and_isFiniteTypeOnCofinalWeakIdealQuotients_iff {φ : B →+* A}
    (hφ : Continuous φ) :
    (φ.IsTaut ∧ φ.IsFiniteTypeOnCofinalWeakIdealQuotients) ↔
      φ.IsTaut ∧ φ.TopologicallyOfFiniteType :=
  sorry

/-- Tautness together with topological finite type is equivalent to `A` being a
closed quotient of `RestrictedPowerSeries (Fin n) B` as a topological `B`-algebra. -/
theorem isTaut_and_topologicallyOfFiniteType_iff_isClosedQuotientOfRestrictedPowerSeries
    {φ : B →+* A} (hφ : Continuous φ) :
    (φ.IsTaut ∧ φ.TopologicallyOfFiniteType) ↔
      φ.IsClosedQuotientOfRestrictedPowerSeries :=
  sorry

end RingHom

namespace TopologicalRing

/-- Lemma 87.29.6 (2): The equivalent conditions of Lemma 87.29.6 define a local
property of arrows of `WAdm^count` in the sense of Situation 87.21.2, i.e. they
satisfy Axioms (1), (2), (3), recorded as `IsLocalMorphismProperty` of
`fun φ ↦ φ.IsTaut ∧ φ.TopologicallyOfFiniteType`. -/
@[stacks 0ANU]
theorem isLocalMorphismProperty_isTaut_and_topologicallyOfFiniteType :
    IsLocalMorphismProperty
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
        [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
        (φ : B →+* A) ↦ φ.IsTaut ∧ φ.TopologicallyOfFiniteType :=
  sorry

end TopologicalRing
