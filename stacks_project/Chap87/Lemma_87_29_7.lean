module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_29_6

/-!
# Taut topologically finite type arrows with admissible source

When the source is admissible, the equivalent conditions of Lemma 87.29.6 are
also equivalent to tautness together with finite type of `φ.closureQuotientMap J`
for some ideal of definition `J`.
-/

@[expose] public section

open TopologicalRing
open TopologicalRing.Ideal

universe u

namespace RingHom

section

variable {B A : Type u} [CommRing B] [TopologicalSpace B]
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- Finite type of the comparison map `φ.closureQuotientMap J` for some ideal of
definition `J` of the source. -/
def IsFiniteTypeOnSomeIdealOfDefinition (φ : B →+* A) : Prop :=
  ∃ J : Ideal B, IsIdealOfDefinition J ∧ (φ.closureQuotientMap J).FiniteType

/-- Finite type on some ideal-of-definition quotient means some ideal of
definition has a finite-type comparison map. -/
theorem isFiniteTypeOnSomeIdealOfDefinition_iff (φ : B →+* A) :
    φ.IsFiniteTypeOnSomeIdealOfDefinition ↔
      ∃ J : Ideal B, IsIdealOfDefinition J ∧ (φ.closureQuotientMap J).FiniteType :=
  sorry

namespace IsFiniteTypeOnSomeIdealOfDefinition

/-- Package finite type of the comparison map at an ideal of definition. -/
theorem of {φ : B →+* A} {J : Ideal B} (hJ : IsIdealOfDefinition J)
    (hft : (φ.closureQuotientMap J).FiniteType) :
    φ.IsFiniteTypeOnSomeIdealOfDefinition :=
  sorry

/-- Finite type on some ideal-of-definition quotient yields an ideal of definition
and finite type of the corresponding comparison map. -/
theorem spec {φ : B →+* A} (h : φ.IsFiniteTypeOnSomeIdealOfDefinition) :
    ∃ J : Ideal B, IsIdealOfDefinition J ∧ (φ.closureQuotientMap J).FiniteType :=
  sorry

end IsFiniteTypeOnSomeIdealOfDefinition

end

section

variable {A B : Type u}
variable [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
variable [CommRing B] [TopologicalSpace B] [IsAdmissibleRing B] [IsCountablyIndexed B]

/-- Lemma 87.29.7: In Lemma 87.29.6 if `B` is admissible (for example adic), then
the equivalent conditions (a)–(d) are also equivalent to (e): `φ : B →+* A` is taut
and `φ.closureQuotientMap J` is of finite type for some ideal of definition `J` of
`B`, where the target ideal is `(Ideal.map φ J).closure`. Adic rings are admissible
via `TopologicalRing.instIsAdmissibleRing`. -/
@[stacks 0CB6]
theorem taut_topologicallyOfFiniteType_tfae_of_isAdmissibleRing {φ : B →+* A}
    (hφ : Continuous φ) :
    List.TFAE
      [φ.IsTaut ∧ φ.IsFiniteTypeOnWeakIdealQuotients,
        φ.IsTaut ∧ φ.IsFiniteTypeOnCofinalWeakIdealQuotients,
        φ.IsTaut ∧ φ.TopologicallyOfFiniteType,
        φ.IsClosedQuotientOfRestrictedPowerSeries,
        φ.IsTaut ∧ φ.IsFiniteTypeOnSomeIdealOfDefinition] :=
  sorry

/-- Tautness together with finite type on some ideal-of-definition quotient is
equivalent to tautness together with topological finite type. -/
theorem isTaut_and_isFiniteTypeOnSomeIdealOfDefinition_iff {φ : B →+* A}
    (hφ : Continuous φ) :
    (φ.IsTaut ∧ φ.IsFiniteTypeOnSomeIdealOfDefinition) ↔
      φ.IsTaut ∧ φ.TopologicallyOfFiniteType :=
  sorry

/-- Tautness together with finite type on every weak-ideal quotient is equivalent
to tautness together with finite type on some ideal-of-definition quotient. -/
theorem isTaut_and_isFiniteTypeOnWeakIdealQuotients_iff_isFiniteTypeOnSomeIdealOfDefinition
    {φ : B →+* A} (hφ : Continuous φ) :
    (φ.IsTaut ∧ φ.IsFiniteTypeOnWeakIdealQuotients) ↔
      φ.IsTaut ∧ φ.IsFiniteTypeOnSomeIdealOfDefinition :=
  sorry

end

end RingHom
