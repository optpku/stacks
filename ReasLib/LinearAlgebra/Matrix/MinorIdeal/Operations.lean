/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Order.Monotone.Basic
public import ReasLib.LinearAlgebra.Matrix.MinorIdeal.Basic

@[expose] public section

/-!
# Operations on Determinantal Ideals

Reusable functoriality, monotonicity, and block-sum interfaces for matrix minor
ideals.

@stack 00N1
@stack 07Z7
-/

universe u v w x y

namespace Matrix

variable {R : Type u} [CommRing R]

/-- A determinant selected by an arbitrary row map belongs to the minor ideal:
noninjective row maps contribute the zero determinant. -/
theorem det_submatrix_mem_minorIdeal_of_rowMap {ι : Type v} {κ : Type w}
    (r : ℕ) (A : Matrix ι κ R) (f : Fin r → ι) (e₂ : Fin r ↪ κ) :
    (A.submatrix f e₂).det ∈ I_(r)(A) := by
  classical
  by_cases hf : Function.Injective f
  · exact Ideal.subset_span ⟨(⟨f, hf⟩, e₂), rfl⟩
  · obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hf
    rw [det_zero_of_row_eq hne (by ext k; exact congrArg (fun a ↦ A a (e₂ k)) hij)]
    exact Ideal.zero_mem _

/-- Increasing the minor size by one can only decrease the associated ideal. -/
theorem minorIdeal_succ_le {ι : Type v} {κ : Type w}
    (r : ℕ) (A : Matrix ι κ R) : I_((r + 1))(A) ≤ I_(r)(A) := by
  classical
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨⟨e₁, e₂⟩, rfl⟩
  change (A.submatrix e₁ e₂).det ∈ I_(r)(A)
  rw [det_succ_row_zero]
  refine Submodule.sum_mem _ fun j _ ↦ Ideal.mul_mem_left _ _ ?_
  exact Ideal.subset_span
    ⟨((Fin.succEmb r).trans e₁, (Fin.succAboveEmb j).trans e₂), rfl⟩

/-- Minor ideals of a fixed matrix are antitone in the minor size. -/
@[stacks 07Z7 "(1), antitonicity of minor ideals"]
theorem minorIdeal_antitone {ι : Type v} {κ : Type w}
    (A : Matrix ι κ R) : Antitone (fun r ↦ I_(r)(A)) :=
  antitone_nat_of_succ_le fun r ↦ minorIdeal_succ_le r A

/-- Deleting `n'` final rows makes the corresponding shifted minor ideal map
into the minor ideal of the remaining initial rows. -/
@[stacks 07Z7 "(2), initial-row minor bound"]
theorem minorIdeal_initialRows_le {n n' m : ℕ} (r : ℕ)
    (B : Matrix (Fin (n + n')) (Fin m) R) :
    I_((r + n'))(B) ≤ I_(r)((B.submatrix (Fin.castAdd n') id)) := by
  classical
  have hstep {k m : ℕ} (s : ℕ) (M : Matrix (Fin (k + 1)) (Fin m) R) :
      I_((s + 1))(M) ≤ I_(s)((M.submatrix Fin.castSucc id)) := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨⟨e₁, e₂⟩, rfl⟩
    change (M.submatrix e₁ e₂).det ∈ I_(s)((M.submatrix Fin.castSucc id))
    obtain ⟨i, hi⟩ : ∃ i : Fin (s + 1),
        ∀ a : Fin s, e₁ (i.succAbove a) ≠ Fin.last k := by
      by_cases h : ∃ i, e₁ i = Fin.last k
      · obtain ⟨i, hi⟩ := h
        refine ⟨i, fun a ha ↦ ?_⟩
        exact Fin.succAbove_ne i a (e₁.injective (ha.trans hi.symm))
      · exact ⟨0, fun a ha ↦ h ⟨(0 : Fin (s + 1)).succAbove a, ha⟩⟩
    rw [det_succ_row _ i]
    refine Submodule.sum_mem _ fun j _ ↦ Ideal.mul_mem_left _ _ ?_
    let f : Fin s → Fin k := fun a ↦ (e₁ (i.succAbove a)).castPred (hi a)
    have hminor := det_submatrix_mem_minorIdeal_of_rowMap s
      (M.submatrix Fin.castSucc id) f ((Fin.succAboveEmb j).trans e₂)
    have hmatrix : (M.submatrix e₁ e₂).submatrix i.succAbove j.succAbove =
        (M.submatrix Fin.castSucc id).submatrix f ((Fin.succAboveEmb j).trans e₂) := by
      ext a b
      change M (e₁ (i.succAbove a)) (e₂ (j.succAbove b)) =
        M (Fin.castSucc ((e₁ (i.succAbove a)).castPred (hi a))) (e₂ (j.succAbove b))
      rw [Fin.castSucc_castPred]
    rw [hmatrix]
    exact hminor
  induction n' with
  | zero =>
    change I_(r)(B) ≤ I_(r)(B)
    exact le_rfl
  | succ n' ih =>
    refine (hstep (r + n') B).trans ?_
    have hmatrix : (B.submatrix Fin.castSucc id).submatrix (Fin.castAdd n') id =
        B.submatrix (Fin.castAdd (n' + 1)) id := by
      ext i j
      rfl
    have h := ih (B.submatrix Fin.castSucc id)
    rw [hmatrix] at h
    exact h

/-- Each chosen minor of a left matrix product belongs to the minor ideal of the
right factor. -/
theorem det_submatrix_mul_left_mem_minorIdeal {ι : Type v} {κ : Type w} [Fintype ι]
    (r : ℕ) (C : Matrix ι ι R) (A : Matrix ι κ R)
    (e₁ : Fin r ↪ ι) (e₂ : Fin r ↪ κ) :
    ((C * A).submatrix e₁ e₂).det ∈ I_(r)(A) := by
  classical
  have hM : (C * A).submatrix e₁ e₂ =
      fun i ↦ ∑ k, C (e₁ i) k • (fun j : Fin r ↦ A k (e₂ j)) := by
    ext i j
    simp [mul_apply]
  rw [hM]
  change (detRowAlternating (n := Fin r) (R := R)).toMultilinearMap _ ∈ _
  rw [MultilinearMap.map_sum]
  refine Submodule.sum_mem _ fun f _ ↦ ?_
  rw [MultilinearMap.map_smul_univ]
  change (∏ i, C (e₁ i) (f i)) * (A.submatrix f e₂).det ∈ _
  exact Ideal.mul_mem_left _ _ (det_submatrix_mem_minorIdeal_of_rowMap r A f e₂)

/-- Left multiplication does not increase a matrix minor ideal. -/
@[stacks 07Z7 "(3), left multiplication of minor ideals"]
theorem minorIdeal_mul_left_le {ι : Type v} {κ : Type w} [Fintype ι]
    (r : ℕ) (C : Matrix ι ι R) (A : Matrix ι κ R) :
    I_(r)((C * A)) ≤ I_(r)(A) := by
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨⟨e₁, e₂⟩, rfl⟩
  exact det_submatrix_mul_left_mem_minorIdeal r C A e₁ e₂

/-- Transposing a matrix preserves each fixed-size minor ideal. -/
@[stacks 00N1 "minor ideals"]
theorem minorIdeal_transpose_eq {ι : Type v} {κ : Type w}
    (r : ℕ) (A : Matrix ι κ R) :
    I_(r)(A.transpose) = I_(r)(A) := by
  apply le_antisymm
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨⟨e₁, e₂⟩, rfl⟩
    change (A.submatrix e₂ e₁).transpose.det ∈ _
    rw [det_transpose]
    exact Ideal.subset_span ⟨(e₂, e₁), rfl⟩
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨⟨e₁, e₂⟩, rfl⟩
    change (A.submatrix e₁ e₂).det ∈ I_(r)(A.transpose)
    rw [← det_transpose]
    exact Ideal.subset_span ⟨(e₂, e₁), rfl⟩

/-- Right multiplication by a square matrix does not increase a fixed-size
minor ideal. -/
@[stacks 00N1 "minor ideals"]
theorem minorIdeal_mul_right_le {ι : Type v} {κ : Type w} [Fintype κ]
    (r : ℕ) (A : Matrix ι κ R) (C : Matrix κ κ R) :
    I_(r)((A * C)) ≤ I_(r)(A) := by
  rw [← minorIdeal_transpose_eq r (A * C), transpose_mul,
    ← minorIdeal_transpose_eq r A]
  exact minorIdeal_mul_left_le r C.transpose A.transpose

/-- Arbitrary maps from a finite square index type give an element of the minor ideal.
Repeated rows or columns contribute zero. -/
private theorem det_submatrix_mem_minorIdeal_of_finiteMaps {α ι κ : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix ι κ R) (f : α → ι) (g : α → κ) :
    (A.submatrix f g).det ∈ minorIdeal (Fintype.card α) A := by
  classical
  let e := (Fintype.equivFin α).symm
  rw [← det_submatrix_equiv_self e (A.submatrix f g)]
  change (A.submatrix (f ∘ e) (g ∘ e)).det ∈ _
  by_cases hg : Function.Injective (g ∘ e)
  · exact det_submatrix_mem_minorIdeal_of_rowMap _ A (f ∘ e) ⟨g ∘ e, hg⟩
  · obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hg
    rw [det_zero_of_column_eq hne (fun k ↦ congrArg (fun c ↦ A (f (e k)) c) hij)]
    exact Ideal.zero_mem _

/-- The minor ideal of a block diagonal matrix is the antidiagonal sum of the
products of the minor ideals of its two diagonal blocks. -/
@[stacks 07Z7 "(4), block-diagonal minor formula"]
theorem minorIdeal_fromBlocks {ι₁ : Type v} {ι₂ : Type w} {κ₁ : Type x} {κ₂ : Type y}
    (r : ℕ) (A₁ : Matrix ι₁ κ₁ R) (A₂ : Matrix ι₂ κ₂ R) :
    I_(r)((fromBlocks A₁ 0 0 A₂)) =
      Finset.sum (Finset.antidiagonal r) fun p ↦ I_(p.1)(A₁) * I_(p.2)(A₂) := by
  classical
  let D := fromBlocks A₁ 0 0 A₂
  apply le_antisymm
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨⟨e₁, e₂⟩, rfl⟩
    change (D.submatrix e₁ e₂).det ∈ _
    by_cases hσ : ∃ σ : Equiv.Perm (Fin r),
        ∀ i, (e₁ (σ i)).isLeft = (e₂ i).isLeft
    · -- A matching of the two block partitions gives a block triangular matrix.
      obtain ⟨σ, hσ⟩ := hσ
      let M := (D.submatrix e₁ e₂).submatrix σ id
      let p : Fin r → Prop := fun i ↦ (e₂ i).isLeft
      have hrow₁ (i : {i // p i}) : (e₁ (σ i)).isLeft := by
        rw [hσ]
        exact i.property
      have hrow₂ (i : {i // ¬p i}) : (e₁ (σ i)).isRight := by
        have hi : ¬(e₁ (σ i)).isLeft := by
          rw [hσ]
          exact i.property
        cases he : e₁ (σ i) <;> simp_all
      have hcol₂ (i : {i // ¬p i}) : (e₂ i).isRight := by
        have hi := i.property
        cases he : e₂ i <;> simp_all [p]
      let f₁ : {i // p i} → ι₁ := fun i ↦ (e₁ (σ i)).getLeft (hrow₁ i)
      let g₁ : {i // p i} → κ₁ := fun i ↦ (e₂ i).getLeft i.property
      let f₂ : {i // ¬p i} → ι₂ := fun i ↦ (e₁ (σ i)).getRight (hrow₂ i)
      let g₂ : {i // ¬p i} → κ₂ := fun i ↦ (e₂ i).getRight (hcol₂ i)
      have hm₁ : toSquareBlockProp M p = A₁.submatrix f₁ g₁ := by
        ext i j
        change D (e₁ (σ i)) (e₂ j) = _
        rw [← Sum.inl_getLeft (e₁ (σ i)) (hrow₁ i),
          ← Sum.inl_getLeft (e₂ j) j.property]
        rfl
      have hm₂ : toSquareBlockProp M (fun i ↦ ¬p i) = A₂.submatrix f₂ g₂ := by
        ext i j
        change D (e₁ (σ i)) (e₂ j) = _
        rw [← Sum.inr_getRight (e₁ (σ i)) (hrow₂ i),
          ← Sum.inr_getRight (e₂ j) (hcol₂ j)]
        rfl
      have hzero : ∀ i, ¬p i → ∀ j, p j → M i j = 0 := by
        intro i hi j hj
        have hi' : ¬(e₁ (σ i)).isLeft := by
          rw [hσ]
          exact hi
        change D (e₁ (σ i)) (e₂ j) = 0
        cases hri : e₁ (σ i) <;> cases hcj : e₂ j <;>
          simp_all [p, D]
      have hmem : M.det ∈ minorIdeal (Fintype.card {i // p i}) A₁ *
          minorIdeal (Fintype.card {i // ¬p i}) A₂ := by
        rw [twoBlockTriangular_det M p hzero, hm₁, hm₂]
        exact Ideal.mul_mem_mul (det_submatrix_mem_minorIdeal_of_finiteMaps A₁ f₁ g₁) (det_submatrix_mem_minorIdeal_of_finiteMaps A₂ f₂ g₂)
      have hcard : Fintype.card {i // p i} + Fintype.card {i // ¬p i} = r := by
        simpa only [Fintype.card_sum, Fintype.card_fin] using
          Fintype.card_congr (Equiv.sumCompl p)
      have hle : minorIdeal (Fintype.card {i // p i}) A₁ * minorIdeal (Fintype.card {i // ¬p i}) A₂ ≤
          Finset.sum (Finset.antidiagonal r) (fun q ↦ I_(q.1)(A₁) * I_(q.2)(A₂)) := by
        rw [Ideal.sum_eq_sup]
        exact Finset.le_sup
          (f := fun q : ℕ × ℕ ↦ minorIdeal q.1 A₁ * minorIdeal q.2 A₂)
          (b := (Fintype.card {i // p i}, Fintype.card {i // ¬p i}))
          (Finset.mem_antidiagonal.mpr hcard)
      have hm : M.submatrix σ.symm id = D.submatrix e₁ e₂ := by
        ext i j
        simp [M, submatrix_apply]
      have hperm := det_permute σ.symm M
      rw [hm] at hperm
      rw [hperm]
      exact Ideal.mul_mem_left _ _ (hle hmem)
    · -- Without such a matching, every Leibniz term crosses a zero block.
      have hdet : (D.submatrix e₁ e₂).det = 0 := by
        rw [det_apply']
        refine Finset.sum_eq_zero fun σ _ ↦ ?_
        obtain ⟨j, hj⟩ := not_forall.mp (fun h ↦ hσ ⟨σ, h⟩)
        have hentry : D (e₁ (σ j)) (e₂ j) = 0 := by
          cases hri : e₁ (σ j) <;> cases hcj : e₂ j <;>
            simp_all [D]
        rw [Finset.prod_eq_zero (Finset.mem_univ j) hentry, mul_zero]
      rw [hdet]
      exact Ideal.zero_mem _
  · -- A product of minors of the blocks is a minor of their block sum.
    rw [Ideal.sum_eq_sup]
    refine Finset.sup_le fun q hq ↦ ?_
    rcases q with ⟨a, b⟩
    have hab : a + b = r := Finset.mem_antidiagonal.mp hq
    change I_(a)(A₁) * I_(b)(A₂) ≤ I_(r)(D)
    rw [minorIdeal, minorIdeal, Ideal.span_mul_span]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨x, ⟨⟨u₁, v₁⟩, rfl⟩, y, ⟨⟨u₂, v₂⟩, rfl⟩, rfl⟩
    have hm : D.submatrix (u₁.sumMap u₂) (v₁.sumMap v₂) =
        fromBlocks (A₁.submatrix u₁ v₁) 0 0 (A₂.submatrix u₂ v₂) := by
      ext i j
      cases i <;> cases j <;> rfl
    have hg := det_submatrix_mem_minorIdeal_of_finiteMaps D (u₁.sumMap u₂) (v₁.sumMap v₂)
    rw [hm, det_fromBlocks_zero₂₁] at hg
    simp only [Fintype.card_sum, Fintype.card_fin, hab] at hg
    exact hg

end Matrix
