/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.GradedMulAction
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Degree-zero parts of homogeneous localized modules

This leaf owns the degree-zero module construction for an arbitrary submonoid of denominators.
Specializations such as localization away from one homogeneous element belong in thin companion
leaves.
-/

@[expose] public section

noncomputable section

universe u v w z

namespace HomogeneousLocalization.Module

variable {ι : Type u} [AddCommMonoid ι] [DecidableEq ι]
variable {S : Type v} [CommRing S]
variable {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
variable (𝒜 : ι → σ) [GradedRing 𝒜]
variable {M : Type z} [AddCommMonoid M] [Module S M]
variable {τ : Type*} [SetLike τ M] [AddSubmonoidClass τ M]

/-- The ordinary localized module is canonically a module over the homogeneous localization at
the same denominator submonoid. -/
@[stacks 00JR "localized module over a homogeneous localization"]
noncomputable instance instLocalizedModule (P : Submonoid S) :
    Module (HomogeneousLocalization 𝒜 P) (LocalizedModule P M) :=
  Module.compHom (LocalizedModule P M)
    (algebraMap (HomogeneousLocalization 𝒜 P) (Localization P))

/-- The carrier of the degree-zero homogeneous localization of a graded module. -/
@[stacks 00JR "degree-zero homogeneous localized module carrier"]
def degreeZeroPartSet (ℳ : ι → τ) [SetLike.GradedSMul 𝒜 ℳ]
    (P : Submonoid S) : Set (LocalizedModule P M) :=
  { z | ∃ i, ∃ m : ℳ i, ∃ s : 𝒜 i, ∃ hs : (s : S) ∈ P,
    z = LocalizedModule.mk (m : M) ⟨(s : S), hs⟩ }

/-- The degree-zero carrier contains zero. -/
@[stacks 00JR "degree-zero homogeneous localized module zero"]
theorem degreeZeroPartSet_zero_mem (ℳ : ι → τ) [SetLike.GradedSMul 𝒜 ℳ]
    (P : Submonoid S) :
    0 ∈ degreeZeroPartSet 𝒜 ℳ P := sorry

/-- The degree-zero carrier is closed under addition. -/
@[stacks 00JR "degree-zero homogeneous localized module addition"]
theorem degreeZeroPartSet_add_mem (ℳ : ι → τ) [SetLike.GradedSMul 𝒜 ℳ]
    (P : Submonoid S) {x y : LocalizedModule P M}
    (hx : x ∈ degreeZeroPartSet 𝒜 ℳ P) (hy : y ∈ degreeZeroPartSet 𝒜 ℳ P) :
    x + y ∈ degreeZeroPartSet 𝒜 ℳ P := sorry

/-- The degree-zero carrier is stable under the homogeneous-localization action. -/
@[stacks 00JR "degree-zero homogeneous localized module scalar closure"]
theorem degreeZeroPartSet_smul_mem (ℳ : ι → τ) [SetLike.GradedSMul 𝒜 ℳ]
    (P : Submonoid S) (z : HomogeneousLocalization 𝒜 P)
    {x : LocalizedModule P M} (hx : x ∈ degreeZeroPartSet 𝒜 ℳ P) :
    z • x ∈ degreeZeroPartSet 𝒜 ℳ P := sorry

/-- The degree-zero part of a graded module after homogeneous localization at `P`. -/
@[stacks 00JR "degree-zero homogeneous localized module"]
noncomputable def degreeZeroPart (ℳ : ι → τ) [SetLike.GradedSMul 𝒜 ℳ]
    (P : Submonoid S) :
    Submodule (HomogeneousLocalization 𝒜 P) (LocalizedModule P M) :=
  { carrier := degreeZeroPartSet 𝒜 ℳ P
    zero_mem' := degreeZeroPartSet_zero_mem 𝒜 ℳ P
    add_mem' := degreeZeroPartSet_add_mem 𝒜 ℳ P
    smul_mem' := degreeZeroPartSet_smul_mem 𝒜 ℳ P }

/-- Membership in the degree-zero part is equivalent to having a fraction representative whose
numerator and denominator have the same grade. -/
@[stacks 00JR "degree-zero homogeneous localized module membership"]
theorem mem_degreeZeroPart_iff (ℳ : ι → τ) [SetLike.GradedSMul 𝒜 ℳ]
    (P : Submonoid S) {z : LocalizedModule P M} :
    z ∈ degreeZeroPart 𝒜 ℳ P ↔
      ∃ i, ∃ m : ℳ i, ∃ s : 𝒜 i, ∃ hs : (s : S) ∈ P,
        z = LocalizedModule.mk (m : M) ⟨(s : S), hs⟩ := sorry

/-- A homogeneous fraction with numerator and denominator in the same grade belongs to the
degree-zero part. -/
@[stacks 00JR "degree-zero homogeneous localized module standard fraction"]
theorem mk_mem_degreeZeroPart (ℳ : ι → τ) [SetLike.GradedSMul 𝒜 ℳ]
    (P : Submonoid S) {i : ι} (m : ℳ i) (s : 𝒜 i) (hs : (s : S) ∈ P) :
    LocalizedModule.mk (m : M) ⟨(s : S), hs⟩ ∈ degreeZeroPart 𝒜 ℳ P := sorry

/-- Every element of the degree-zero part has a representative whose numerator and denominator
have the same grade. -/
@[stacks 00JR "degree-zero homogeneous localized module representative"]
theorem exists_mk_eq (ℳ : ι → τ) [SetLike.GradedSMul 𝒜 ℳ]
    (P : Submonoid S) (z : degreeZeroPart 𝒜 ℳ P) :
    ∃ i, ∃ m : ℳ i, ∃ s : 𝒜 i, ∃ hs : (s : S) ∈ P,
      (z : LocalizedModule P M) = LocalizedModule.mk (m : M) ⟨(s : S), hs⟩ := sorry

/-- The natural map from a smaller ordinary localization to a larger one preserves the
degree-zero carrier. -/
@[stacks 00JR "degree-zero homogeneous localization denominator enlargement"]
theorem liftOfLE_mem_degreeZeroPart (ℳ : ι → τ) [SetLike.GradedSMul 𝒜 ℳ]
    (P Q : Submonoid S) (hPQ : P ≤ Q) {z : LocalizedModule P M}
    (hz : z ∈ degreeZeroPart 𝒜 ℳ P) :
    LocalizedModule.liftOfLE P Q hPQ z ∈ degreeZeroPart 𝒜 ℳ Q := sorry

end HomogeneousLocalization.Module
