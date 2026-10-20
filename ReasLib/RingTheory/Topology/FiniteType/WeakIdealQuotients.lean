/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.FiniteType
public import ReasLib.RingTheory.Topology.WeaklyAdmissible
public import ReasLib.Topology.Algebra.Ring.FaithfullyFlatOpenQuotients

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
  rfl

/-- Finite type of every weak-ideal reduction `φ.closureQuotientMap J`. -/
def IsFiniteTypeOnWeakIdealQuotients (φ : B →+* A) : Prop :=
  ∀ J : Ideal B, IsWeakIdealOfDefinition J → (φ.closureQuotientMap J).FiniteType

/-- Finite type on weak-ideal quotients means every weak-ideal comparison map is
of finite type. -/
theorem isFiniteTypeOnWeakIdealQuotients_iff (φ : B →+* A) :
    φ.IsFiniteTypeOnWeakIdealQuotients ↔
      ∀ J : Ideal B, IsWeakIdealOfDefinition J → (φ.closureQuotientMap J).FiniteType :=
  Iff.rfl

namespace IsFiniteTypeOnWeakIdealQuotients

/-- Package pointwise finite type of weak-ideal comparison maps. -/
theorem of {φ : B →+* A}
    (h : ∀ J : Ideal B, IsWeakIdealOfDefinition J → (φ.closureQuotientMap J).FiniteType) :
    φ.IsFiniteTypeOnWeakIdealQuotients :=
  h

/-- Finite type on weak-ideal quotients yields finite type of each comparison
map `φ.closureQuotientMap J`. -/
theorem spec {φ : B →+* A} (h : φ.IsFiniteTypeOnWeakIdealQuotients) {J : Ideal B}
    (hJ : IsWeakIdealOfDefinition J) : (φ.closureQuotientMap J).FiniteType :=
  h J hJ

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
  Iff.rfl

namespace IsFiniteTypeOnCofinalWeakIdealQuotients

/-- Package a cofinal weak-ideal family with finite-type comparison maps. -/
theorem of {ι : Type u} {φ : B →+* A} (J : ι → Ideal B)
    (hJ : ∀ i, IsWeakIdealOfDefinition (J i))
    (hcof : ∀ K, IsWeakIdealOfDefinition K → ∃ i, J i ≤ K)
    (hft : ∀ i, (φ.closureQuotientMap (J i)).FiniteType) :
    φ.IsFiniteTypeOnCofinalWeakIdealQuotients :=
  ⟨ι, J, hJ, hcof, hft⟩

/-- Finite type on a cofinal system yields a cofinal family of weak ideals of
definition and finite type of each comparison map. -/
theorem spec {φ : B →+* A} (h : φ.IsFiniteTypeOnCofinalWeakIdealQuotients) :
    ∃ (ι : Type u) (J : ι → Ideal B),
      (∀ i, IsWeakIdealOfDefinition (J i)) ∧
        (∀ K, IsWeakIdealOfDefinition K → ∃ i, J i ≤ K) ∧
          ∀ i, (φ.closureQuotientMap (J i)).FiniteType :=
  h

end IsFiniteTypeOnCofinalWeakIdealQuotients

/-- Finite type of the comparison map `φ.closureQuotientMap J` for some ideal of
definition `J` of the source. -/
def IsFiniteTypeOnSomeIdealOfDefinition (φ : B →+* A) : Prop :=
  ∃ J : Ideal B, IsIdealOfDefinition J ∧ (φ.closureQuotientMap J).FiniteType

/-- Finite type on some ideal-of-definition quotient means some ideal of
definition has a finite-type comparison map. -/
theorem isFiniteTypeOnSomeIdealOfDefinition_iff (φ : B →+* A) :
    φ.IsFiniteTypeOnSomeIdealOfDefinition ↔
      ∃ J : Ideal B, IsIdealOfDefinition J ∧ (φ.closureQuotientMap J).FiniteType :=
  Iff.rfl

namespace IsFiniteTypeOnSomeIdealOfDefinition

/-- Finite type of the comparison map at an ideal of definition implies finite
type on some ideal-of-definition quotient. -/
theorem of {φ : B →+* A} {J : Ideal B} (hJ : IsIdealOfDefinition J)
    (hft : (φ.closureQuotientMap J).FiniteType) :
    φ.IsFiniteTypeOnSomeIdealOfDefinition :=
  ⟨J, hJ, hft⟩

/-- Finite type on some ideal-of-definition quotient yields an ideal of definition
and finite type of the corresponding comparison map. -/
theorem spec {φ : B →+* A} (h : φ.IsFiniteTypeOnSomeIdealOfDefinition) :
    ∃ J : Ideal B, IsIdealOfDefinition J ∧ (φ.closureQuotientMap J).FiniteType :=
  h

end IsFiniteTypeOnSomeIdealOfDefinition

end RingHom

