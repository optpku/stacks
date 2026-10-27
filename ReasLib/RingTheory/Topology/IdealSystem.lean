/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.Adic.Basic

/-!
# Fundamental systems of ideals of definition
-/

@[expose] public section

universe u

open Topology

namespace TopologicalRing

/-- Ideals of definition of a commutative topological ring. -/
abbrev IdealOfDefinition (A : Type u) [CommRing A] [TopologicalSpace A] :=
  {I : Ideal A // Ideal.IsIdealOfDefinition I}

/-- Bundle an ideal with its ideal-of-definition property. -/
def IdealOfDefinition.of {A : Type u} [CommRing A] [TopologicalSpace A]
    (I : Ideal A) (hI : Ideal.IsIdealOfDefinition I) : IdealOfDefinition A :=
  ⟨I, hI⟩

/-- Bundling an ideal retains its underlying ideal and its defining property. -/
theorem IdealOfDefinition.of_spec {A : Type u} [CommRing A] [TopologicalSpace A]
    (I : Ideal A) (hI : Ideal.IsIdealOfDefinition I) :
    (IdealOfDefinition.of I hI).val = I ∧
      Ideal.IsIdealOfDefinition (IdealOfDefinition.of I hI).val :=
  ⟨rfl, hI⟩

namespace Ideal

/-- An open subideal of an ideal of definition is an ideal of definition. -/
theorem isIdealOfDefinition_of_le_isOpen {A : Type u} [CommRing A]
    [TopologicalSpace A] {I J : Ideal A}
    (hI : IsIdealOfDefinition I) (hJ : IsOpen (J : Set A)) (hJI : J ≤ I) :
    IsIdealOfDefinition J := by
  refine ⟨hJ, fun U hU ↦ ?_⟩
  obtain ⟨n, hn⟩ := hI.2 U hU
  exact ⟨n, fun x hx ↦ hn ((pow_le_pow_left' hJI n) hx)⟩

/-- A fundamental system consists of ideals of definition forming a basis at zero. -/
def IsFundamentalSystemOfIdeals {A : Type u} [CommRing A] [TopologicalSpace A]
    {ι : Type u} (I : ι → Ideal A) : Prop :=
  (∀ i, IsIdealOfDefinition (I i)) ∧
    (nhds (0 : A)).HasBasis (fun _ : ι ↦ True) (fun i ↦ (I i : Set A))

/-- A family is fundamental exactly when its members are defining ideals and form a basis. -/
theorem isFundamentalSystemOfIdeals_iff {A : Type u} [CommRing A]
    [TopologicalSpace A] {ι : Type u} (I : ι → Ideal A) :
    IsFundamentalSystemOfIdeals I ↔
      (∀ i, IsIdealOfDefinition (I i)) ∧
        (nhds (0 : A)).HasBasis (fun _ : ι ↦ True) (fun i ↦ (I i : Set A)) :=
  Iff.rfl

/-- All ideals of definition of a pre-admissible ring form a fundamental system. -/
theorem isFundamentalSystemOfIdeals_idealOfDefinition {A : Type u}
    [CommRing A] [TopologicalSpace A] [IsPreadmissibleRing A] :
    IsFundamentalSystemOfIdeals (fun J : IdealOfDefinition A ↦ J.val) :=
  sorry

end Ideal

end TopologicalRing
