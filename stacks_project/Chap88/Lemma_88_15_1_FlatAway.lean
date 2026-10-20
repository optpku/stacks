/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Topology.Algebra.TopologicallyNilpotent
public import ReasLib.RingTheory.Topology.Adic.Complete
public import stacks_project.Chap87.Lemma_87_6_2_IsAdic
public import stacks_project.Chap88.Lemma_88_14_1_RigClosed

public import ReasLib.RingTheory.Flat.Adic

/-!
# Flatness after inverting topologically nilpotent elements

The flatness predicates and ideal-avoidance API are provided by their shared owners.
-/

universe u

#check (Ideal.ContainsNoIdealOfDefinition :
  ∀ {A : Type u} [CommRing A] [TopologicalSpace A], Ideal A → Prop)
