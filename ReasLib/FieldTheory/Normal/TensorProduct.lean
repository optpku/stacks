/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open scoped TensorProduct
open IntermediateField

noncomputable section

universe u

namespace FieldExtension

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

local notation "N" => IntermediateField.normalClosure K L (AlgebraicClosure L)
local notation "ιN" => IntermediateField.val N

section EmbeddingIndexed

variable [Fintype (Field.Emb K L)]

/-- The canonical comparison map from the embedding-indexed tensor product of conjugate copies
of `L` to its normal closure in `AlgebraicClosure L`. -/
noncomputable def piTensorProductToNormalClosure : (⨂[K] _ : Field.Emb K L, L) →ₐ[K] N :=
  let e : (L →ₐ[K] N) ≃ Field.Emb K L := normalClosure.algHomEquiv K L (AlgebraicClosure L)
  PiTensorProduct.liftAlgHom
    ((MultilinearMap.mkPiAlgebra K (Field.Emb K L) N).compLinearMap
      fun σ ↦ (e.symm σ).toLinearMap)
    (by simp [MultilinearMap.compLinearMap_apply])
    (by
      intro x y
      simp [MultilinearMap.compLinearMap_apply, Finset.prod_mul_distrib])

/-- On a pure tensor, `piTensorProductToNormalClosure` multiplies the images of its entries under
all `K`-embeddings of `L` into `AlgebraicClosure L`. -/
@[simp]
theorem piTensorProductToNormalClosure_tprod (x : Field.Emb K L → L) :
    ((piTensorProductToNormalClosure K L) (PiTensorProduct.tprod K x) : AlgebraicClosure L) =
      ∏ σ : Field.Emb K L, σ (x σ) := by
  classical
  let e : (L →ₐ[K] N) ≃ Field.Emb K L := normalClosure.algHomEquiv K L (AlgebraicClosure L)
  change ιN ((piTensorProductToNormalClosure K L) (PiTensorProduct.tprod K x)) = _
  unfold piTensorProductToNormalClosure
  rw [PiTensorProduct.liftAlgHom, AlgHom.ofLinearMap_apply, PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply, map_prod]
  refine Finset.prod_congr rfl fun σ _ ↦ ?_
  exact congrArg (fun f : Field.Emb K L ↦ f (x σ)) (e.apply_symm_apply σ)

end EmbeddingIndexed

/-- A reindexed tensor-product map with the expected pure-tensor formula is surjective onto the
normal closure. -/
private theorem surjectiveOfTprodFormula {ι : Type*} [Fintype ι]
    (e : ι ≃ Field.Emb K L) (φ : (⨂[K] _ : ι, L) →ₐ[K] N)
    (hφ : ∀ x : ι → L,
      (φ (PiTensorProduct.tprod K x) : AlgebraicClosure L) = ∏ i, e i (x i)) :
    Function.Surjective φ := by
  classical
  let _ : Finite (Field.Emb K L) := Finite.of_equiv ι e
  let _ : Fintype (Field.Emb K L) := Fintype.ofFinite (Field.Emb K L)
  have hKL : Algebra.IsAlgebraic K L := by
    by_contra hKL
    -- Local instance justification (proof-local temporary data): record the contrary transcendence hypothesis.
    letI : Algebra.Transcendental K L :=
      (Algebra.transcendental_iff_not_isAlgebraic).2 hKL
    -- Local instance justification (proof-local temporary data): derive infinitude of embeddings from transcendence.
    letI : Infinite (Field.Emb K L) := Field.infinite_emb_of_transcendental K L
    exact Finite.false (Finite.of_fintype (Field.Emb K L))
  -- Local instance justification (proof-local temporary data): make the established algebraicity fact available to typeclass search.
  letI : Algebra.IsAlgebraic K L := hKL
  -- Local instance justification (proof-local temporary data): compose algebraicity through the algebraic closure.
  letI : Algebra.IsAlgebraic K (AlgebraicClosure L) :=
    Algebra.IsAlgebraic.trans K L (AlgebraicClosure L)
  -- Local instance justification (proof-local temporary data): restrict algebraicity to the normal-closure subfield.
  letI : Algebra.IsAlgebraic K N := Algebra.IsAlgebraic.of_injective ιN Subtype.val_injective
  let eSub : Subalgebra K N ≃o IntermediateField K N := subalgebraEquivIntermediateField
  let R : IntermediateField K N := eSub φ.range
  have hRsub : R.toSubalgebra = φ.range := by
    ext x
    change x ∈ eSub φ.range ↔ x ∈ φ.range
    simp [eSub]
  have htop : R = ⊤ := by
    apply map_injective ιN
    refine le_antisymm ?_ ?_
    · exact map_mono ιN le_top
    · rw [← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val]
      refine normalClosure_le_iff.2 fun σ ↦ ?_
      intro y hy
      rcases (AlgHom.mem_fieldRange).1 hy with ⟨x, rfl⟩
      change σ x ∈ (R.map ιN).toSubalgebra
      rw [toSubalgebra_map, hRsub, Subalgebra.mem_map]
      refine ⟨φ (PiTensorProduct.tprod K (Pi.mulSingle (e.symm σ) x)), AlgHom.mem_range_self φ _, ?_⟩
      change (φ (PiTensorProduct.tprod K (Pi.mulSingle (e.symm σ) x)) : AlgebraicClosure L) = σ x
      have hmulSingle :
          (fun i ↦ e i ((Pi.mulSingle (e.symm σ) x : ι → L) i)) =
            (Pi.mulSingle (e.symm σ) (σ x) : ι → AlgebraicClosure L) := by
        ext i
        by_cases h : i = e.symm σ
        · subst h
          simp
        · simp [Pi.mulSingle, h]
      calc
        (φ (PiTensorProduct.tprod K (Pi.mulSingle (e.symm σ) x)) : AlgebraicClosure L) =
            ∏ i, e i ((Pi.mulSingle (e.symm σ) x : ι → L) i) := hφ _
        _ = ∏ i, (Pi.mulSingle (e.symm σ) (σ x) : ι → AlgebraicClosure L) i := by
          rw [hmulSingle]
        _ = σ x := Fintype.prod_pi_mulSingle' (e.symm σ) (σ x)
  have hrange : φ.range = ⊤ := by
    rw [← hRsub, htop]
    rfl
  exact (AlgHom.range_eq_top φ).mp hrange

section EmbeddingIndexed

variable [Fintype (Field.Emb K L)]

/-- The embedding-indexed comparison map onto the normal closure is surjective. -/
theorem surjectivePiTensorProductToNormalClosure :
    Function.Surjective (piTensorProductToNormalClosure K L) := by
  exact surjectiveOfTprodFormula K L (Equiv.refl (Field.Emb K L))
    (piTensorProductToNormalClosure K L)
    (piTensorProductToNormalClosure_tprod K L)

end EmbeddingIndexed

section FiniteDegreeBridge

variable [FiniteDimensional K L]

/-- The finite embedding count is the natural-number realization of `Field.sepDegree K L`. -/
private theorem natCardEmbEqToNatSepDegree :
    Nat.card (Field.Emb K L) = Cardinal.toNat (Field.sepDegree K L) := by
  calc
    Nat.card (Field.Emb K L) = Field.finSepDegree K L := by
      symm
      exact Field.finSepDegree_eq_of_isAlgClosed K L (AlgebraicClosure L)
    _ = Cardinal.toNat (Field.sepDegree K L) := Field.finSepDegree_eq K L

/-- A chosen reindexing of `Fin (Cardinal.toNat (Field.sepDegree K L))` by the `K`-embeddings of
`L` into `AlgebraicClosure L`. -/
private noncomputable def sepDegreeEmbEquiv :
    Fin (Cardinal.toNat (Field.sepDegree K L)) ≃ Field.Emb K L := by
  refine (Fintype.equivFinOfCardEq ?_).symm
  rw [Fintype.card_eq_nat_card]
  exact natCardEmbEqToNatSepDegree K L

/-- Reindex the constant-family tensor product by an equivalence of finite index types. -/
private noncomputable def piTensorProductReindexAlgEquiv {ι : Type*} [Fintype ι]
    (e : ι ≃ Field.Emb K L) : (⨂[K] _ : ι, L) ≃ₐ[K] (⨂[K] _ : Field.Emb K L, L) :=
  AlgEquiv.ofLinearEquiv
    (PiTensorProduct.reindex K (fun _ : ι ↦ L) e)
    (by
      rw [PiTensorProduct.one_def, PiTensorProduct.one_def, PiTensorProduct.reindex_tprod]
      rfl)
    (by
      intro x y
      induction x using PiTensorProduct.induction_on with
      | smul_tprod r f =>
          induction y using PiTensorProduct.induction_on with
          | smul_tprod s g =>
              simp [PiTensorProduct.tprod_mul_tprod, Pi.mul_def]
          | add y₁ y₂ hy₁ hy₂ =>
              rw [mul_add, map_add, map_add, hy₁, hy₂, mul_add]
      | add x₁ x₂ hx₁ hx₂ =>
          rw [add_mul, map_add, map_add, hx₁, hx₂, add_mul])

/-- Lemma 9.16.6 (Tag 0EXL): the finite tensor product of
`Cardinal.toNat (Field.sepDegree K L)` copies of `L` over `K` surjects onto the normal closure of
`L/K` inside `AlgebraicClosure L`. -/
theorem existsSurjectivePiTensorProductToNormalClosure :
    ∃ φ : (⨂[K] _ : Fin (Cardinal.toNat (Field.sepDegree K L)), L) →ₐ[K] N,
      Function.Surjective φ := by
  let φ : (⨂[K] _ : Fin (Cardinal.toNat (Field.sepDegree K L)), L) →ₐ[K] N :=
    (piTensorProductToNormalClosure K L).comp
      (piTensorProductReindexAlgEquiv K L (sepDegreeEmbEquiv K L)).toAlgHom
  refine ⟨φ, ?_⟩
  exact (surjectivePiTensorProductToNormalClosure K L).comp
    (piTensorProductReindexAlgEquiv K L (sepDegreeEmbEquiv K L)).surjective

end FiniteDegreeBridge

end FieldExtension
