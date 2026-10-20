/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Topology.WeaklyAdmissible.Taut

/-!
# Lemma 87.5.2

A continuous homomorphism of weakly admissible topological rings is taut if and
only if the closures of the extensions of weak ideals of definition of the
source form a fundamental system of weak ideals of definition of the target.
-/

@[expose] public section

open scoped Topology
open TopologicalRing
open TopologicalRing.Ideal

universe u v

/- Lemma 87.5.2: Let `φ : A →+* B` be a continuous homomorphism of weakly
admissible topological rings. Then `φ` is taut if and only if, for every weak
ideal of definition `I` of `A`, the closure of `Ideal.map φ I` is a weak ideal
of definition of `B`, and these closures are cofinal among weak ideals of
definition of `B`. -/
@[stacks 0AMY] #check (RingHom.isTaut_iff_weakIdealOfDefinition :
  ∀ {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B]
    {φ : A →+* B} (hφ : Continuous φ),
    φ.IsTaut ↔
      (∀ I : Ideal A, IsWeakIdealOfDefinition I →
          IsWeakIdealOfDefinition (Ideal.map φ I).closure) ∧
        ∀ J : Ideal B, IsWeakIdealOfDefinition J →
          ∃ I : Ideal A, IsWeakIdealOfDefinition I ∧ (Ideal.map φ I).closure ≤ J)

/- If `φ` is a continuous taut homomorphism of weakly admissible topological
rings, then the closure of the extension of every weak ideal of definition of
the source is a weak ideal of definition of the target. -/
#check (TopologicalRing.Ideal.IsWeakIdealOfDefinition.map_closure_of_isTaut :
  ∀ {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B]
    {φ : A →+* B}, Continuous φ → φ.IsTaut →
    ∀ {I : Ideal A}, IsWeakIdealOfDefinition I →
      IsWeakIdealOfDefinition (Ideal.map φ I).closure)

/- If `φ` is a continuous taut homomorphism of weakly admissible topological
rings, then every weak ideal of definition of the target contains the closure of
the extension of some weak ideal of definition of the source. -/
#check (RingHom.IsTaut.exists_weakIdealOfDefinition_closure_map_le :
  ∀ {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B]
    {φ : A →+* B}, Continuous φ → φ.IsTaut →
    ∀ {J : Ideal B}, IsWeakIdealOfDefinition J →
      ∃ I : Ideal A, IsWeakIdealOfDefinition I ∧ (Ideal.map φ I).closure ≤ J)

/- A continuous homomorphism of weakly admissible topological rings is taut if
and only if the closures of the extensions of weak ideals of definition of the
source are themselves weak ideals of definition and form a neighborhood basis
of `0` in the target. -/
#check (RingHom.isTaut_iff_hasBasis_weakIdealOfDefinition :
  ∀ {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B]
    {φ : A →+* B} (hφ : Continuous φ),
    φ.IsTaut ↔
      (∀ I : Ideal A, IsWeakIdealOfDefinition I →
          IsWeakIdealOfDefinition (Ideal.map φ I).closure) ∧
        (nhds (0 : B)).HasBasis (fun I : Ideal A ↦ IsWeakIdealOfDefinition I)
          (fun I ↦ ((Ideal.map φ I).closure : Set B)))
