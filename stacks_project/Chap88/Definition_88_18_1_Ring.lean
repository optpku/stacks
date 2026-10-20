/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Noetherian.Basic
public import ReasLib.RingTheory.Topology.Adic.Complete
public import stacks_project.Chap87.Lemma_87_6_2_IsAdic
public import stacks_project.Chap88.«88_2_0_2_TopologicallyFiniteType»
public import stacks_project.Chap88.«88_3_0_1»
public import ReasLib.RingTheory.AdicCompletion.RigSmooth

/-!
# Rig-smooth algebras and continuous homomorphisms

An algebra over a Noetherian pair `(A, I)` is rig-smooth when it is
topologically of finite type and some power of `I` annihilates
`Ext¹_B(NL_{B/A}^∧, N)` for every `B`-module `N`. A continuous homomorphism of
adic Noetherian topological rings is rig-smooth when this holds for some,
equivalently any, ideal of definition of `A` that also induces the ambient
topology on `B`.
-/

@[expose] public section

universe u

#check (Algebra.RigSmooth :
  ∀ {A : Type u} [CommRing A] (I : Ideal A) (B : Type u) [CommRing B]
    [Algebra A B], Prop)

#check (RingHom.RigSmooth :
  ∀ {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B], (A →+* B) → Prop)
