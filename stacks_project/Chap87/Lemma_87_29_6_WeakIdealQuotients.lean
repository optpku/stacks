module

public import Mathlib.RingTheory.FiniteType
public import stacks_project.Chap87.Definition_87_4_8_WeaklyAdmissible
public import stacks_project.Chap87.Lemma_87_8_3_OpenQuotient

/-!
# Finite type on weak-ideal quotients

A homomorphism `φ : B →+* A` is of finite type on weak-ideal quotients when each
induced map `B ⧸ J →+* A ⧸ (Ideal.map φ J).closure` is of finite type, for every
weak ideal of definition `J` of `B`, or along some cofinal family of such ideals.
-/

@[expose] public section

universe u

open TopologicalRing
open TopologicalRing.Ideal

namespace RingHom

variable {B A : Type u} [CommRing B] [TopologicalSpace B]
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The comparison map `B ⧸ J →+* A ⧸ I` induced by `φ : B →+* A`, where `I` is
the closure of `Ideal.map φ J`. -/
def closureQuotientMap (φ : B →+* A) (J : Ideal B) :
    B ⧸ J →+* A ⧸ (Ideal.map φ J).closure :=
  Ideal.quotientMap (Ideal.map φ J).closure φ (le_comap_closure_map φ J)

/-- `closureQuotientMap` is `Ideal.quotientMap` along `le_comap_closure_map`. -/
theorem closureQuotientMap_def (φ : B →+* A) (J : Ideal B) :
    φ.closureQuotientMap J =
      Ideal.quotientMap (Ideal.map φ J).closure φ (le_comap_closure_map φ J) :=
  sorry

/-- Finite type of every weak-ideal reduction `φ.closureQuotientMap J`. -/
def IsFiniteTypeOnWeakIdealQuotients (φ : B →+* A) : Prop :=
  ∀ J : Ideal B, IsWeakIdealOfDefinition J → (φ.closureQuotientMap J).FiniteType

/-- Finite type on weak-ideal quotients means every weak-ideal comparison map is
of finite type. -/
theorem isFiniteTypeOnWeakIdealQuotients_iff (φ : B →+* A) :
    φ.IsFiniteTypeOnWeakIdealQuotients ↔
      ∀ J : Ideal B, IsWeakIdealOfDefinition J → (φ.closureQuotientMap J).FiniteType :=
  sorry

namespace IsFiniteTypeOnWeakIdealQuotients

/-- Package pointwise finite type of weak-ideal comparison maps. -/
theorem of {φ : B →+* A}
    (h : ∀ J : Ideal B, IsWeakIdealOfDefinition J → (φ.closureQuotientMap J).FiniteType) :
    φ.IsFiniteTypeOnWeakIdealQuotients :=
  sorry

/-- Finite type on weak-ideal quotients yields finite type of each comparison
map `φ.closureQuotientMap J`. -/
theorem spec {φ : B →+* A} (h : φ.IsFiniteTypeOnWeakIdealQuotients) {J : Ideal B}
    (hJ : IsWeakIdealOfDefinition J) : (φ.closureQuotientMap J).FiniteType :=
  sorry

end IsFiniteTypeOnWeakIdealQuotients

/-- Finite type of weak-ideal reductions along some cofinal family of weak ideals
of definition of the source. -/
def IsFiniteTypeOnCofinalWeakIdealQuotients (φ : B →+* A) : Prop :=
  ∃ (ι : Type u) (J : ι → Ideal B),
    (∀ i, IsWeakIdealOfDefinition (J i)) ∧
      (∀ K, IsWeakIdealOfDefinition K → ∃ i, J i ≤ K) ∧
        ∀ i, (φ.closureQuotientMap (J i)).FiniteType

/-- Finite type on a cofinal weak-ideal system is existence of a cofinal family of
weak ideals of definition with finite-type comparison maps. -/
theorem isFiniteTypeOnCofinalWeakIdealQuotients_iff (φ : B →+* A) :
    φ.IsFiniteTypeOnCofinalWeakIdealQuotients ↔
      ∃ (ι : Type u) (J : ι → Ideal B),
        (∀ i, IsWeakIdealOfDefinition (J i)) ∧
          (∀ K, IsWeakIdealOfDefinition K → ∃ i, J i ≤ K) ∧
            ∀ i, (φ.closureQuotientMap (J i)).FiniteType :=
  sorry

namespace IsFiniteTypeOnCofinalWeakIdealQuotients

/-- Package a cofinal weak-ideal family with finite-type comparison maps. -/
theorem of {ι : Type u} {φ : B →+* A} (J : ι → Ideal B)
    (hJ : ∀ i, IsWeakIdealOfDefinition (J i))
    (hcof : ∀ K, IsWeakIdealOfDefinition K → ∃ i, J i ≤ K)
    (hft : ∀ i, (φ.closureQuotientMap (J i)).FiniteType) :
    φ.IsFiniteTypeOnCofinalWeakIdealQuotients :=
  sorry

/-- Finite type on a cofinal system yields a cofinal family of weak ideals of
definition and finite type of each comparison map. -/
theorem spec {φ : B →+* A} (h : φ.IsFiniteTypeOnCofinalWeakIdealQuotients) :
    ∃ (ι : Type u) (J : ι → Ideal B),
      (∀ i, IsWeakIdealOfDefinition (J i)) ∧
        (∀ K, IsWeakIdealOfDefinition K → ∃ i, J i ≤ K) ∧
          ∀ i, (φ.closureQuotientMap (J i)).FiniteType :=
  sorry

end IsFiniteTypeOnCofinalWeakIdealQuotients

end RingHom

