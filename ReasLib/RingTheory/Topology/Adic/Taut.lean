/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Finiteness.Ideal
public import ReasLib.RingTheory.Topology.Adic.Basic
public import ReasLib.RingTheory.Topology.Adic.Complete
public import ReasLib.RingTheory.Topology.Adic.Hom
public import ReasLib.Topology.Algebra.Ring.Taut

/-!
# Taut homomorphisms and ideals of definition
-/

@[expose] public section

universe u v

open TopologicalRing
open scoped Topology

namespace RingHom.IsTaut

/-- The closure of the extension of an ideal of definition along a continuous taut
homomorphism is an ideal of definition. -/
theorem isIdealOfDefinition_closure_map {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut) {I : Ideal A}
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    TopologicalRing.Ideal.IsIdealOfDefinition (Ideal.map φ I).closure := by
  have hpow : ∀ n : ℕ, (Ideal.map φ I).closure ^ n ≤ ((Ideal.map φ I) ^ n).closure := by
    intro n
    induction n with
    | zero =>
        simp only [pow_zero]
        exact fun _ hx ↦ subset_closure hx
    | succ n ih =>
        rw [pow_succ, pow_succ]
        refine Ideal.mul_le.mpr ?_
        intro a ha b hb
        have hab : ∀ b ∈ Ideal.map φ I,
            a * b ∈ (((Ideal.map φ I) ^ n) * Ideal.map φ I).closure := by
          intro b hb
          exact map_mem_closure (f := fun x : B ↦ x * b) (continuous_mul_const b) (ih ha)
            (fun x hx ↦ Ideal.mul_mem_mul hx hb)
        exact closure_minimal hab (isClosed_closure.preimage (continuous_const_mul a)) hb
  refine ⟨?_, ?_⟩
  · exact (Ideal.map φ I).closure.toAddSubgroup.isOpen_of_mem_nhds
      (htaut.mem_iff.mpr ⟨I, hI.1, Set.Subset.rfl⟩)
  · intro U hU
    obtain ⟨K, hK, hKU⟩ := htaut.mem_iff.mp hU
    obtain ⟨n, hn⟩ := hI.2 _ (hK.mem_nhds K.zero_mem)
    refine ⟨n, ?_⟩
    have hp : (Ideal.map φ I).closure ^ n ≤ (Ideal.map φ (I ^ n)).closure := by
      simpa only [Ideal.map_pow] using hpow n
    exact fun b hb ↦ hKU (closure_mono (Ideal.map_mono hn) (hp hb))

/-- Pre-admissibility ascends along a continuous taut homomorphism of linearly
topologized rings. -/
theorem isPreadmissibleRing {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsPreadmissibleRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut) :
    IsPreadmissibleRing B := by
  obtain ⟨I, hI⟩ := IsPreadmissibleRing.exists_ideal_isIdealOfDefinition (R := A)
  exact { exists_ideal_isIdealOfDefinition :=
    ⟨(Ideal.map φ I).closure, htaut.isIdealOfDefinition_closure_map hcont hI⟩ }

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [TopologicalSpace A] [IsPreadicRing A]
variable [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
variable [T2Space B] [@CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B)]

/-- The extension of any finitely generated ideal of definition along a continuous taut
homomorphism from a pre-adic ring to a complete separated linearly topologized ring
induces the target topology. -/
theorem isAdic_map {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut)
    {I : Ideal A} (hIfg : I.FG) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    IsAdic (Ideal.map φ I) :=
  sorry

/-- The target of a continuous taut homomorphism from a pre-adic ring with a finitely
generated ideal of definition to a complete separated linearly topologized ring is adic. -/
@[stacks 0APU]
theorem isAdicRing {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut)
    (hAfg : ∃ I : Ideal A, I.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition I) :
    IsAdicRing B := by
  obtain ⟨I, hIfg, hI⟩ := hAfg
  have hmap := isAdic_map hcont htaut hIfg hI
  letI : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B
  letI : IsUniformAddGroup B := isUniformAddGroup_of_addCommGroup
  exact { exists_ideal_isAdicComplete :=
    ⟨Ideal.map φ I, hmap, hmap.isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩⟩ }

/-- The target of a continuous taut homomorphism from a pre-adic ring with a finitely
generated ideal of definition to a complete separated linearly topologized ring has a
finitely generated ideal of definition. -/
@[stacks 0APU]
theorem exists_fg_isIdealOfDefinition {φ : A →+* B} (hcont : Continuous φ)
    (htaut : φ.IsTaut)
    (hAfg : ∃ I : Ideal A, I.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition I) :
    ∃ J : Ideal B, J.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition J := by
  obtain ⟨I, hIfg, hI⟩ := hAfg
  have hmap := isAdic_iff.mp (isAdic_map hcont htaut hIfg hI)
  refine ⟨Ideal.map φ I, hIfg.map φ, ?_, hmap.2⟩
  simpa only [pow_one] using hmap.1 1

/-- A continuous taut homomorphism from a pre-adic ring with a finitely generated ideal
of definition to a complete separated linearly topologized ring admits a source ideal
of definition whose extension induces the target topology. -/
@[stacks 0APU]
theorem exists_isAdic_map {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut)
    (hAfg : ∃ I : Ideal A, I.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition I) :
    ∃ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I ∧
      IsAdic (Ideal.map φ I) := by
  obtain ⟨I, hIfg, hI⟩ := hAfg
  exact ⟨I, hI, isAdic_map hcont htaut hIfg hI⟩

end

/-- A continuous taut homomorphism of pre-adic rings with complete separated target
and a finitely generated source ideal of definition is adic. -/
theorem isAdicHom {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsPreadicRing A]
    [CommRing B] [TopologicalSpace B] [IsPreadicRing B] [T2Space B]
    [@CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B)]
    {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut)
    (hAfg : ∃ I : Ideal A, I.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition I) :
    φ.IsAdicHom := by
  exact exists_isAdic_map hcont htaut hAfg

end RingHom.IsTaut
