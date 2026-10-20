/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.WeaklyAdmissible.Composition
public import stacks_project.Chap87.«87_21_2_1_LocalizeSquare»

/-!
# Stability under composition for morphisms of WAdm^count

The composition-stability predicate and its specification and application theorems
are available through their mathematical owner.
-/

@[expose] public section

universe u

open TopologicalRing

#check (TopologicalRing.IsStableUnderComposition :
    (∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B],
    (B →+* A) → Prop) → Prop)

#check (TopologicalRing.isStableUnderComposition_iff :
    ∀ (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B],
    (B →+* A) → Prop),
    IsStableUnderComposition P ↔
      ∀ {A B C : Type u}
        [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
        [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
        [CommRing C] [TopologicalSpace C] [IsWeaklyAdmissibleRing C] [IsCountablyIndexed C]
        (φ : B →+* A) (ψ : C →+* B),
        Continuous φ → Continuous ψ → P φ → P ψ → P (φ.comp ψ))

#check (TopologicalRing.IsStableUnderComposition.comp :
    ∀ (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B],
    (B →+* A) → Prop)
    {A B C : Type u}
    [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
    [CommRing C] [TopologicalSpace C] [IsWeaklyAdmissibleRing C] [IsCountablyIndexed C]
    (_ : IsStableUnderComposition P) (φ : B →+* A) (ψ : C →+* B)
    (_ : Continuous φ) (_ : Continuous ψ) (_ : P φ) (_ : P ψ),
    P (φ.comp ψ))
