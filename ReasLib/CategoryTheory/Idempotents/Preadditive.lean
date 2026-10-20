/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Kernels
public import Mathlib.CategoryTheory.Preadditive.Opposite
public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Idempotent Completeness in Preadditive Categories

This file extends Mathlib's kernel criterion for `IsIdempotentComplete` by its dual cokernel
criterion and by the corresponding binary-biproduct normal form for an idempotent.
-/

@[expose] public section

open Opposite

universe v u

namespace CategoryTheory.Idempotents

open Limits

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A preadditive category is idempotent complete if and only if every idempotent endomorphism
has a cokernel. -/
@[stacks 09SH]
theorem isIdempotentComplete_iff_idempotents_have_cokernels (C : Type u)
    [Category.{v} C] [Preadditive C] :
    IsIdempotentComplete C ↔
      ∀ (Z : C) (p : End Z), p ≫ p = p → HasCokernel p := by
  constructor
  · intro h Z p hp
    have hk : HasKernel p.op :=
      (isIdempotentComplete_iff_idempotents_have_kernels Cᵒᵖ).1
        (isIdempotentComplete_iff_opposite.2 h) (op Z) p.op
        (by simpa using congrArg Quiver.Hom.op hp)
    -- Local instance justification (proof-local temporary data): the opposite-kernel witness is
    -- used only to invoke the canonical kernel projections while constructing the dual cokernel.
    have w : p ≫ (kernel.ι p.op).unop = 0 := by
      have h := congrArg Quiver.Hom.unop (kernel.condition p.op)
      change p.op.unop ≫ (kernel.ι p.op).unop = 0 at h
      simpa using h
    refine ⟨⟨CokernelCofork.ofπ (kernel.ι p.op).unop w, ?_⟩⟩
    exact KernelFork.IsLimit.ofιUnop (kernel.ι p.op) (kernel.condition p.op)
      (kernelIsKernel p.op)
  · intro h
    apply isIdempotentComplete_iff_opposite.1
    rw [isIdempotentComplete_iff_idempotents_have_kernels]
    intro Z p hp
    -- Local instance justification (proof-local temporary data): the assumed cokernel of `p.unop`
    -- is used only through Mathlib's canonical cokernel API to build its opposite kernel.
    let : HasCokernel p.unop := h Z.unop p.unop (by simpa using congrArg Quiver.Hom.unop hp)
    have w : (cokernel.π p.unop).op ≫ p = 0 := by
      have hπ := congrArg Quiver.Hom.op (cokernel.condition p.unop)
      change (cokernel.π p.unop).op ≫ p = 0 at hπ
      simpa using hπ
    refine ⟨⟨KernelFork.ofι (cokernel.π p.unop).op w, ?_⟩⟩
    exact CokernelCofork.IsColimit.ofπOp (cokernel.π p.unop) (cokernel.condition p.unop)
      (cokernelIsCokernel p.unop)

/-- In an idempotent-complete preadditive category, every idempotent becomes the projection onto
the second summand after a suitable binary-biproduct decomposition. -/
@[stacks 09SH]
theorem idempotentIsSecondSummandProjection [IsIdempotentComplete C] {Z : C}
    (p : Z ⟶ Z) (hp : p ≫ p = p) :
    ∃ (X Y : C) (_ : HasBinaryBiproduct X Y) (e : X ⊞ Y ≅ Z),
      p = e.inv ≫ biprod.snd ≫ biprod.inr ≫ e.hom := by
  rcases IsIdempotentComplete.idempotents_split Z (𝟙 Z - p)
      (idem_of_id_sub_idem p hp) with
    ⟨X, i, a, hi, ha⟩
  rcases IsIdempotentComplete.idempotents_split Z p hp with ⟨Y, j, q, hj, hq⟩
  have hjp : j ≫ p = j := by
    calc
      j ≫ p = j ≫ (q ≫ j) := by rw [hq]
      _ = j := by rw [← Category.assoc, hj, Category.id_comp]
  have hpj : j ≫ a = 0 := by
    have hjzero : j ≫ (𝟙 Z - p) = 0 := by
      simp [hjp]
    have h : j ≫ a ≫ i = 0 := by
      rw [ha]
      exact hjzero
    have h' : j ≫ a ≫ i ≫ a = 0 := by
      simpa [Category.assoc] using congrArg (fun f ↦ f ≫ a) h
    simpa [Category.assoc, hi] using h'
  have hqi : i ≫ q = 0 := by
    have h : i ≫ (𝟙 Z - p) = i := by
      calc
        i ≫ (𝟙 Z - p) = i ≫ (a ≫ i) := by rw [ha]
        _ = (i ≫ a) ≫ i := by rw [← Category.assoc]
        _ = i := by rw [hi, Category.id_comp]
    have hip : i ≫ p = 0 := by
      have h' : i + -(i ≫ p) = i := by
        simpa [sub_eq_add_neg, Category.assoc] using h
      have h'' := congrArg (fun f ↦ -i + f) h'
      simpa [add_assoc] using h''
    have h' : i ≫ q ≫ j = 0 := by
      rw [hq]
      exact hip
    have h'' : i ≫ q ≫ j ≫ q = 0 := by
      simpa [Category.assoc] using congrArg (fun f ↦ f ≫ q) h'
    simpa [Category.assoc, hj] using h''
  have htotal : a ≫ i + q ≫ j = 𝟙 Z := by
    rw [ha, hq, sub_add_cancel]
  let b : BinaryBicone X Y :=
    { pt := Z
      fst := a
      snd := q
      inl := i
      inr := j
      inl_fst := hi
      inl_snd := hqi
      inr_fst := hpj
      inr_snd := hj }
  -- Local instance justification (proof-local temporary data): this noncanonical biproduct is
  -- constructed from the two chosen splittings and is returned explicitly by the existential.
  letI : HasBinaryBiproduct X Y := hasBinaryBiproduct_of_total b htotal
  refine ⟨X, Y, ‹HasBinaryBiproduct X Y›,
    (biprod.uniqueUpToIso X Y (isBinaryBilimitOfTotal b htotal)).symm, ?_⟩
  calc
    p = q ≫ j := hq.symm
    _ = biprod.lift a q ≫ biprod.snd ≫ biprod.inr ≫ biprod.desc i j := by
      simp

/-- Idempotent completeness, existence of cokernels of idempotents, and the binary-biproduct
projection normal form are equivalent in a preadditive category. -/
@[stacks 09SH]
theorem karoubian_tfae :
    List.TFAE
      [ IsIdempotentComplete C
      , ∀ (Z : C) (p : End Z), p ≫ p = p → HasCokernel p
      , ∀ (Z : C) (p : End Z), p ≫ p = p →
          ∃ (X Y : C) (_ : HasBinaryBiproduct X Y) (e : X ⊞ Y ≅ Z),
            p = e.inv ≫ biprod.snd ≫ biprod.inr ≫ e.hom
      ] := by
  tfae_have 1 ↔ 2 := by
    exact isIdempotentComplete_iff_idempotents_have_cokernels C
  tfae_have 1 → 3 := by
    intro h Z p hp
    exact @idempotentIsSecondSummandProjection C _ _ h Z p hp
  tfae_have 3 → 1 := by
    intro h
    refine ⟨?_⟩
    intro Z p hp
    rcases h Z p hp with ⟨X, Y, _, e, rfl⟩
    refine ⟨Y, biprod.inr ≫ e.hom, e.inv ≫ biprod.snd, ?_, ?_⟩
    · simp
    · simp [Category.assoc]
  tfae_finish

end CategoryTheory.Idempotents
