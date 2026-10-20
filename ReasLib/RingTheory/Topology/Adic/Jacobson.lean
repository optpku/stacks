/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Noetherian.Basic
public import ReasLib.RingTheory.Topology.Adic.Complete

/-!
# Jacobson special fibers of adic rings

For an adic Noetherian topological ring, Jacobsonness of the quotient by an
ideal of definition is independent of the chosen ideal of definition.
-/

@[expose] public section

universe u

/-- For an adic Noetherian topological ring, `A ⧸ I` is Jacobson for some
ideal of definition if and only if it is Jacobson for every ideal of
definition. -/
theorem isJacobsonRing_quotient_isIdealOfDefinition_iff {A : Type u}
    [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsAdicRing A] [IsNoetherianRing A] :
    (∃ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I ∧
        IsJacobsonRing (A ⧸ I)) ↔
      ∀ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I →
        IsJacobsonRing (A ⧸ I) :=
  sorry
