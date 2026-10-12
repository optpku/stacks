/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.CentralSimple.Splitting.Separable
public import ReasLib.Algebra.CentralSimple.Splitting.Degree
public import ReasLib.FieldTheory.Normal.Closure
public import Mathlib.Algebra.Azumaya.Basic
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleModule.IsAlgClosed
public import Mathlib.RingTheory.TotallySplit

/-! # TFAE Characterization of Finite Central Simple Algebras

Six equivalent characterizations of finite central simple algebras:
finite-dimensional + central + simple; center = k with trivial two-sided ideals;
split over algebraic closure; split over separable closure; split by a finite
Galois extension; matrix algebra over a central division algebra.

## Main declarations

- `CSA.isSplitBy_algebraicClosure` — every CSA splits over the algebraic closure
- `CSA.isSplitBy_separableClosure` — every CSA splits over the separable closure
- `CSA.isSplitBy_of_isScalarTower` — splitness ascends along field towers
- `CSA.exists_finite_galois_splitting_field` — finite Galois splitting field exists
- `CSA.exists_finite_separable_splitting_field` — finite separable splitting in universe v
- `CSA.splitting_tfae` — the 6-way TFAE statement

## References

- [Stacks Project, Tag 0753](https://stacks.math.columbia.edu/tag/0753)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

section

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]

-- Local instance justification (noncanonical choice): select the right extension-field action; global registration conflicts with the left action when the tensor factors coincide.
attribute [local instance] Algebra.TensorProduct.rightAlgebra

-- ============================================================
-- Private helpers for the reverse direction (3 → 1)
-- ============================================================

private lemma isCentral_of_algEquiv_across_universes
    {K : Type u} [CommSemiring K] {D : Type v} {D' : Type w}
    [Semiring D] [Algebra K D] [Semiring D'] [Algebra K D']
    [h : Algebra.IsCentral K D] (e : D ≃ₐ[K] D') : Algebra.IsCentral K D' := by
  refine ⟨fun x hx ↦ ?_⟩
  obtain ⟨c, hc⟩ :=
    Algebra.mem_bot.1 (h.out ((MulEquivClass.apply_mem_center_iff e.symm).mpr hx))
  rw [Algebra.mem_bot]
  exact ⟨c, by simpa using congrArg e hc⟩

private lemma split_over_algebraicClosure_implies_upstairs_finite_central_simple
    (h :
      ∃ n : ℕ, n ≠ 0 ∧ Nonempty
        ((A ⊗[k] AlgebraicClosure k) ≃ₐ[AlgebraicClosure k]
          Matrix (Fin n) (Fin n) (AlgebraicClosure k))) :
    FiniteDimensional (AlgebraicClosure k) (A ⊗[k] AlgebraicClosure k) ∧
      Algebra.IsCentral (AlgebraicClosure k) (A ⊗[k] AlgebraicClosure k) ∧
      IsSimpleRing (A ⊗[k] AlgebraicClosure k) := by
  rcases h with ⟨n, hn, ⟨e⟩⟩
  letI : NeZero n := ⟨hn⟩
  have hfinite :
      FiniteDimensional (AlgebraicClosure k) (A ⊗[k] AlgebraicClosure k) := by
    exact e.symm.toLinearEquiv.finiteDimensional
  have hcentral :
      Algebra.IsCentral (AlgebraicClosure k) (A ⊗[k] AlgebraicClosure k) := by
    letI :
        Algebra.IsCentral (AlgebraicClosure k)
          (Matrix (Fin n) (Fin n) (AlgebraicClosure k)) := inferInstance
    exact isCentral_of_algEquiv_across_universes e.symm
  have hsimple :
      IsSimpleRing (A ⊗[k] AlgebraicClosure k) := by
    have hMatrix :
        IsSimpleRing (Matrix (Fin n) (Fin n) (AlgebraicClosure k)) := inferInstance
    exact IsSimpleRing.of_ringEquiv e.symm.toRingEquiv hMatrix
  exact ⟨hfinite, hcentral, hsimple⟩

private lemma split_over_algebraicClosure_implies_finiteDimensional
    (h :
      ∃ n : ℕ, n ≠ 0 ∧ Nonempty
        ((A ⊗[k] AlgebraicClosure k) ≃ₐ[AlgebraicClosure k]
          Matrix (Fin n) (Fin n) (AlgebraicClosure k))) :
    FiniteDimensional k A := by
  rcases split_over_algebraicClosure_implies_upstairs_finite_central_simple (k := k) (A := A) h with
    ⟨hfiniteUpstairs, _, _⟩
  letI : FiniteDimensional (AlgebraicClosure k) (A ⊗[k] AlgebraicClosure k) := hfiniteUpstairs
  have hfiniteComm :
      FiniteDimensional (AlgebraicClosure k) ((AlgebraicClosure k) ⊗[k] A) :=
    (Algebra.TensorProduct.commRight k (AlgebraicClosure k) A).symm.toLinearEquiv.finiteDimensional
  letI : FiniteDimensional (AlgebraicClosure k) ((AlgebraicClosure k) ⊗[k] A) := hfiniteComm
  letI : Module.FaithfullyFlat k (AlgebraicClosure k) := inferInstance
  letI : Module.Finite (AlgebraicClosure k) ((AlgebraicClosure k) ⊗[k] A) := inferInstance
  letI : Module.Finite k A :=
    Module.Finite.of_finite_tensorProduct_of_faithfullyFlat (AlgebraicClosure k)
  infer_instance

private lemma finite_central_simple_iff_center_bot_and_two_sided_ideal_trivial :
    (FiniteDimensional k A ∧ Algebra.IsCentral k A ∧ IsSimpleRing A) ↔
      (FiniteDimensional k A ∧ Subalgebra.center k A = ⊥ ∧
        Nontrivial A ∧ ∀ I : Ideal A, I.IsTwoSided → I = ⊥ ∨ I = ⊤) := by
  constructor
  · rintro ⟨hfinite, hcentral, hsimple⟩
    letI : Algebra.IsCentral k A := hcentral
    obtain ⟨hnontrivial, htrivial⟩ := isSimpleRing_iff_isTwoSided_imp.mp hsimple
    exact ⟨hfinite, Algebra.IsCentral.center_eq_bot k A, hnontrivial, htrivial⟩
  · rintro ⟨hfinite, hcenter, hnontrivial, htrivial⟩
    have hcentral : Algebra.IsCentral k A := ⟨hcenter.le⟩
    have hsimple : IsSimpleRing A := isSimpleRing_iff_isTwoSided_imp.mpr ⟨hnontrivial, htrivial⟩
    exact ⟨hfinite, hcentral, hsimple⟩

private lemma finite_central_simple_iff_matrix_division_form :
    (FiniteDimensional k A ∧ Algebra.IsCentral k A ∧ IsSimpleRing A) ↔
      (∃ (n : ℕ), n ≠ 0 ∧ ∃ (D : Type v) (_ : DivisionRing D) (_ : Algebra k D)
        (_ : FiniteDimensional k D) (_ : Algebra.IsCentral k D),
        Nonempty (A ≃ₐ[k] Matrix (Fin n) (Fin n) D)) := by
  constructor
  · rintro ⟨hfinite, hcentral, hsimple⟩
    letI : FiniteDimensional k A := hfinite
    letI : Algebra.IsCentral k A := hcentral
    letI : IsSimpleRing A := hsimple
    letI : IsArtinianRing A := IsArtinianRing.of_finite k A
    obtain ⟨n, hn, D, hDdiv, hDalg, hDfinite, ⟨e⟩⟩ :=
      IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite k A
    letI : NeZero n := hn
    letI : DivisionRing D := hDdiv
    letI : Algebra k D := hDalg
    letI : Module.Finite k D := hDfinite
    letI : FiniteDimensional k D := inferInstance
    letI : Algebra.IsCentral k (Matrix (Fin n) (Fin n) D) :=
      Algebra.IsCentral.of_algEquiv k A _ e
    -- Local instance justification (proof-local temporary data): D and n come from this existential Wedderburn decomposition; centrality descends from its matrix model, and n is not inferable from a global instance target Algebra.IsCentral k D.
    letI : Algebra.IsCentral k D := Algebra.IsCentral.of_matrix (k := k) n D
    exact ⟨n, hn.out, D, inferInstance, inferInstance, inferInstance, inferInstance, ⟨e⟩⟩
  · rintro ⟨n, hn, D, hDdiv, hDalg, hDfinite, hDcentral, ⟨e⟩⟩
    letI : DivisionRing D := hDdiv
    letI : Algebra k D := hDalg
    letI : FiniteDimensional k D := hDfinite
    letI : Algebra.IsCentral k D := hDcentral
    letI : NeZero n := ⟨hn⟩
    have hfinite : FiniteDimensional k A := by
      exact e.symm.toLinearEquiv.finiteDimensional
    have hcentral : Algebra.IsCentral k A := by
      letI : Algebra.IsCentral k (Matrix (Fin n) (Fin n) D) := inferInstance
      exact Algebra.IsCentral.of_algEquiv k (Matrix (Fin n) (Fin n) D) A e.symm
    have hsimple : IsSimpleRing A := by
      have hmatrix : IsSimpleRing (Matrix (Fin n) (Fin n) D) := inferInstance
      exact IsSimpleRing.of_ringEquiv e.symm.toRingEquiv hmatrix
    exact ⟨hfinite, hcentral, hsimple⟩

private lemma tensor_baseChange_eq_bot_or_eq_top_of_two_sided
    (h :
      ∃ n : ℕ, n ≠ 0 ∧ Nonempty
        ((A ⊗[k] AlgebraicClosure k) ≃ₐ[AlgebraicClosure k]
          Matrix (Fin n) (Fin n) (AlgebraicClosure k)))
    (I : Ideal A) (hI : I.IsTwoSided) :
    (((I.restrictScalars k).baseChange (AlgebraicClosure k) :
      Submodule (AlgebraicClosure k) ((AlgebraicClosure k) ⊗[k] A)) = ⊥) ∨
      (((I.restrictScalars k).baseChange (AlgebraicClosure k) :
        Submodule (AlgebraicClosure k) ((AlgebraicClosure k) ⊗[k] A)) = ⊤) := by
  let K := AlgebraicClosure k
  rcases split_over_algebraicClosure_implies_upstairs_finite_central_simple (k := k) (A := A) h with
    ⟨_, _, hsimpleUpstairs⟩
  haveI : IsSimpleRing (K ⊗[k] A) :=
    IsSimpleRing.of_ringEquiv (Algebra.TensorProduct.comm k A K).toRingEquiv hsimpleUpstairs
  have hJmul :
      ∀ x ∈ I.map (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A),
        ∀ b, x * b ∈ I.map (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A) := by
    intro x hx
    rw [Ideal.map, ← Ideal.submodule_span_eq] at hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨i, hi, rfl⟩ b
      induction b using TensorProduct.induction_on with
      | zero => simpa using Ideal.zero_mem _
      | tmul c y =>
          have hmul :
              (Algebra.TensorProduct.includeRight (R := k) (A := K) (B := A)) i *
                  (c ⊗ₜ[k] y) =
                (c ⊗ₜ[k] (1 : A)) *
                  (Algebra.TensorProduct.includeRight (R := k) (A := K) (B := A)) (i * y) := by
            simp [Algebra.TensorProduct.tmul_mul_tmul]
          rw [hmul]
          exact Ideal.mul_mem_left _ _
            (Ideal.mem_map_of_mem _ (hI.mul_mem_of_left y hi))
      | add b₁ b₂ hb₁ hb₂ =>
          rw [mul_add]
          exact Ideal.add_mem _ hb₁ hb₂
    · intro b
      simpa using Ideal.zero_mem _
    · intro x y _ _ hx hy b
      rw [add_mul]
      exact Ideal.add_mem _ (hx b) (hy b)
    · intro r x _ hx b
      rw [smul_eq_mul, mul_assoc]
      exact Ideal.mul_mem_left _ _ (hx b)
  haveI hJtwo :
      (I.map (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A)).IsTwoSided :=
    ⟨fun b hx ↦ hJmul _ hx b⟩
  have hbase :
      (((I.restrictScalars k).baseChange K :
          Submodule K (K ⊗[k] A))).restrictScalars k =
        (I.map (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A)).restrictScalars k := by
    rw [Ideal.map_includeRight_eq (R := k) (A := K) I]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, rfl⟩
  rcases (isSimpleRing_iff_isTwoSided_imp.mp (inferInstance : IsSimpleRing (K ⊗[k] A))).2
      (I.map (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A)) hJtwo with hbot | htop
  · left
    refine Submodule.restrictScalars_injective k _ _ ?_
    exact hbase.trans (by rw [hbot, Submodule.restrictScalars_bot, Submodule.restrictScalars_bot])
  · right
    refine Submodule.restrictScalars_injective k _ _ ?_
    exact hbase.trans (by rw [htop, Submodule.restrictScalars_top, Submodule.restrictScalars_top])

private lemma finrank_baseChange_submodule_eq
    (K : Type u) [Field K] [Algebra k K] {M : Type v} [AddCommGroup M] [Module k M]
    (p : Submodule k M) :
    Module.finrank K (p.baseChange K) = Module.finrank K (K ⊗[k] p) := by
  have hinj : Function.Injective (p.subtype.baseChange K) :=
    TensorProduct.map_injective_of_flat_flat (LinearMap.id : K →ₗ[k] K) p.subtype
      (fun _ _ hxy ↦ hxy) p.injective_subtype
  exact LinearMap.finrank_range_of_inj hinj

private lemma center_finrank_eq_one_of_split_algebraicClosure
    [FiniteDimensional k A] [IsSimpleRing A]
    (h :
      ∃ n : ℕ, n ≠ 0 ∧ Nonempty
        ((A ⊗[k] AlgebraicClosure k) ≃ₐ[AlgebraicClosure k]
          Matrix (Fin n) (Fin n) (AlgebraicClosure k))) :
    Module.finrank k (Subalgebra.center k A) = 1 := by
  let K := AlgebraicClosure k
  let C := Subalgebra.center k A
  rcases split_over_algebraicClosure_implies_upstairs_finite_central_simple (k := k) (A := A) h with
    ⟨hfiniteUpstairs, hcentralUpstairs, hsimpleUpstairs⟩
  letI : FiniteDimensional K (A ⊗[k] K) := hfiniteUpstairs
  letI : FiniteDimensional K (K ⊗[k] A) :=
    (Algebra.TensorProduct.commRight k K A).symm.toLinearEquiv.finiteDimensional
  letI : Algebra.IsCentral K (A ⊗[k] K) := hcentralUpstairs
  letI : Algebra.IsCentral K (K ⊗[k] A) :=
    isCentral_of_algEquiv_across_universes (Algebra.TensorProduct.commRight k K A).symm
  haveI : IsSimpleRing (K ⊗[k] A) :=
    IsSimpleRing.of_ringEquiv (Algebra.TensorProduct.comm k A K).toRingEquiv hsimpleUpstairs
  have hcenterField : FiniteDimensional k C ∧ IsField C :=
    sorry /- center_finiteFieldExtension (k := k) (A := A) -/
  letI : FiniteDimensional k C := hcenterField.1
  haveI : Nontrivial C := ⟨hcenterField.2.exists_pair_ne⟩
  have hNle :
      (Subalgebra.toSubmodule C : Submodule k A).baseChange K ≤
        Subalgebra.toSubmodule (Subalgebra.center K (K ⊗[k] A)) := by
    rintro _ ⟨y, rfl⟩
    induction y using TensorProduct.induction_on with
    | zero =>
        rw [map_zero]
        exact Submodule.zero_mem _
    | tmul c z =>
        simp only [LinearMap.baseChange_tmul, Submodule.coe_subtype]
        rw [Subalgebra.mem_toSubmodule, Subalgebra.mem_center_iff]
        intro w
        induction w using TensorProduct.induction_on with
        | zero => rw [zero_mul, mul_zero]
        | tmul c' a' =>
            have hz : ∀ b : A, b * (z : A) = (z : A) * b :=
              Subalgebra.mem_center_iff.mp
                (show (z : A) ∈ Subalgebra.center k A from z.2)
            rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
              mul_comm c' c, hz a']
        | add w₁ w₂ hw₁ hw₂ => rw [add_mul, mul_add, hw₁, hw₂]
    | add y₁ y₂ hy₁ hy₂ =>
        rw [map_add]
        exact Submodule.add_mem _ hy₁ hy₂
  have hcenterK :
      Module.finrank K (Subalgebra.toSubmodule (Subalgebra.center K (K ⊗[k] A))) = 1 := by
    have hbot : Subalgebra.center K (K ⊗[k] A) = ⊥ :=
      Algebra.IsCentral.center_eq_bot K (K ⊗[k] A)
    rw [hbot, Algebra.toSubmodule_bot, Submodule.one_eq_span,
      finrank_span_singleton (one_ne_zero (α := K ⊗[k] A))]

  have hfinrankN :
      Module.finrank K ((Subalgebra.toSubmodule C : Submodule k A).baseChange K) =
        Module.finrank k C :=
    (finrank_baseChange_submodule_eq (k := k) K (Subalgebra.toSubmodule C)).trans
      Module.finrank_baseChange
  have hle : Module.finrank k C ≤ 1 := by
    calc
      Module.finrank k C
          = Module.finrank K ((Subalgebra.toSubmodule C : Submodule k A).baseChange K) :=
            hfinrankN.symm
      _ ≤ Module.finrank K
            (Subalgebra.toSubmodule (Subalgebra.center K (K ⊗[k] A))) :=
            Submodule.finrank_mono hNle
      _ = 1 := hcenterK
  have hge : 1 ≤ Module.finrank k C := Module.finrank_pos
  exact le_antisymm hle hge

private lemma split_over_algebraicClosure_implies_two_sided_ideal_trivial
    (h :
      ∃ n : ℕ, n ≠ 0 ∧ Nonempty
        ((A ⊗[k] AlgebraicClosure k) ≃ₐ[AlgebraicClosure k]
          Matrix (Fin n) (Fin n) (AlgebraicClosure k))) :
    ∀ I : Ideal A, I.IsTwoSided → I = ⊥ ∨ I = ⊤ := by
  let K := AlgebraicClosure k
  have hfinite : FiniteDimensional k A :=
    split_over_algebraicClosure_implies_finiteDimensional (k := k) (A := A) h
  letI : FiniteDimensional k A := hfinite
  letI : Module.FaithfullyFlat k K := inferInstance
  intro I hI
  rcases tensor_baseChange_eq_bot_or_eq_top_of_two_sided (k := k) (A := A) h I hI with
    hBaseBot | hBaseTop
  · left
    ext x
    constructor
    · intro hx
      have hxBase :
          (1 : K) ⊗ₜ[k] x ∈ ((I.restrictScalars k).baseChange K :
            Submodule K (K ⊗[k] A)) :=
        Submodule.tmul_mem_baseChange_of_mem (1 : K) hx
      rw [hBaseBot] at hxBase
      have hxZero : (1 : K) ⊗ₜ[k] x = 0 := by simpa using hxBase
      have hmk_inj :
          Function.Injective (TensorProduct.mk k K A 1) :=
        Module.FaithfullyFlat.tensorProduct_mk_injective (A := k) (B := K) A
      have hx' : x = 0 := hmk_inj (by simpa using hxZero)
      exact Ideal.mem_bot.mpr hx'
    · intro hx
      obtain rfl := Ideal.mem_bot.mp hx
      exact I.zero_mem
  · right
    have hfinI :
        Module.finrank k (I.restrictScalars k) = Module.finrank k A := by
      calc
        Module.finrank k (I.restrictScalars k)
            = Module.finrank K (K ⊗[k] ↥(I.restrictScalars k)) :=
              (Module.finrank_baseChange (R := K) (S := k)
                (M' := ↥(I.restrictScalars k))).symm
        _ = Module.finrank K ((I.restrictScalars k).baseChange K) :=
              (finrank_baseChange_submodule_eq (k := k) K (I.restrictScalars k)).symm
        _ = Module.finrank K (K ⊗[k] A) := by
              rw [hBaseTop]
              exact LinearEquiv.finrank_eq Submodule.topEquiv
        _ = Module.finrank k A := Module.finrank_baseChange
    have htop : I.restrictScalars k = ⊤ := Submodule.eq_top_of_finrank_eq hfinI
    refine Submodule.restrictScalars_injective k _ _ ?_
    simp only [htop, Submodule.restrictScalars_top]

private lemma split_over_algebraicClosure_implies_isSimpleRing
    (h :
      ∃ n : ℕ, n ≠ 0 ∧ Nonempty
        ((A ⊗[k] AlgebraicClosure k) ≃ₐ[AlgebraicClosure k]
          Matrix (Fin n) (Fin n) (AlgebraicClosure k))) :
    IsSimpleRing A := by
  have hnontrivial : Nontrivial A := by
    rcases h with ⟨n, hn, ⟨e⟩⟩
    letI : NeZero n := ⟨hn⟩
    letI : Nontrivial (A ⊗[k] AlgebraicClosure k) := e.toEquiv.nontrivial
    refine ⟨1, 0, fun h10 ↦ ?_⟩
    have hzero : (1 : A ⊗[k] AlgebraicClosure k) = 0 := by
      calc
        (1 : A ⊗[k] AlgebraicClosure k)
            = (1 : A) ⊗ₜ[k] (1 : AlgebraicClosure k) := Algebra.TensorProduct.one_def
        _ = (0 : A) ⊗ₜ[k] (1 : AlgebraicClosure k) := by rw [h10]
        _ = 0 := TensorProduct.zero_tmul _ _
    exact one_ne_zero hzero
  exact isSimpleRing_iff_isTwoSided_imp.mpr
    ⟨hnontrivial, split_over_algebraicClosure_implies_two_sided_ideal_trivial (k := k) (A := A) h⟩

private lemma split_over_algebraicClosure_implies_isCentral
    [FiniteDimensional k A] [IsSimpleRing A]
    (h :
      ∃ n : ℕ, n ≠ 0 ∧ Nonempty
        ((A ⊗[k] AlgebraicClosure k) ≃ₐ[AlgebraicClosure k]
          Matrix (Fin n) (Fin n) (AlgebraicClosure k))) :
    Algebra.IsCentral k A := by
  let C := Subalgebra.center k A
  have hfinrankC : Module.finrank k C = 1 :=
    center_finrank_eq_one_of_split_algebraicClosure (k := k) (A := A) h
  have hbij : Function.Bijective (algebraMap k C) :=
    Module.Free.bijective_algebraMap_of_finrank_eq_one hfinrankC
  refine ⟨fun x hx ↦ ?_⟩
  obtain ⟨a, ha⟩ := hbij.2 ⟨x, hx⟩
  rw [Algebra.mem_bot]
  refine ⟨a, ?_⟩
  exact congrArg Subtype.val ha

namespace CSA

/-- Iterated scalar extension along `k → L → K` identifies with extension directly to `K`. -/
private noncomputable def cancelBaseChangeAlgEquiv
    {B : Type v} [Ring B] [Algebra k B] (L : Type*) (K : Type*) [Field L] [Field K]
    [Algebra k L] [Algebra k K] [Algebra L K] [IsScalarTower k L K] :
    K ⊗[L] (L ⊗[k] B) ≃ₐ[K] K ⊗[k] B :=
  AlgEquiv.symm <|
    AlgEquiv.ofLinearEquiv
      (TensorProduct.AlgebraTensorModule.cancelBaseChange k L K K B).symm
      (by simp [Algebra.TensorProduct.one_def])
      (LinearMap.map_mul_of_map_mul_tmul fun x₁ x₂ b₁ b₂ ↦ by
        simp [Algebra.TensorProduct.tmul_mul_tmul])

/-- Scalar extension of an `n × n` matrix algebra over `L` is the matrix algebra over `K`. -/
private noncomputable def matrix_baseChange_algEquiv
    {L : Type*} {K : Type*} [Field L] [Field K] [Algebra k L] [Algebra k K]
    [Algebra L K] [IsScalarTower k L K] (n : ℕ) :
    K ⊗[L] Matrix (Fin n) (Fin n) L ≃ₐ[K] Matrix (Fin n) (Fin n) K :=
  let eK : K ≃ₐ[K] Matrix (Fin 1) (Fin 1) K :=
    ((Matrix.reindexAlgEquiv K K finOneEquiv).trans Matrix.uniqueAlgEquiv).symm
  let eTensor :
      K ⊗[L] Matrix (Fin n) (Fin n) L ≃ₐ[K]
        Matrix (Fin 1) (Fin 1) K ⊗[L] Matrix (Fin n) (Fin n) L :=
    Algebra.TensorProduct.congr eK
      (AlgEquiv.refl : Matrix (Fin n) (Fin n) L ≃ₐ[L] Matrix (Fin n) (Fin n) L)
  let eKronecker :
      Matrix (Fin 1) (Fin 1) K ⊗[L] Matrix (Fin n) (Fin n) L ≃ₐ[K]
        Matrix (Fin 1 × Fin n) (Fin 1 × Fin n) (K ⊗[L] L) :=
    Matrix.kroneckerTMulAlgEquiv (Fin 1) (Fin n) L K K L
  let eCoeff :
      Matrix (Fin 1 × Fin n) (Fin 1 × Fin n) (K ⊗[L] L) ≃ₐ[K]
        Matrix (Fin 1 × Fin n) (Fin 1 × Fin n) K :=
    (Algebra.TensorProduct.rid L K K).mapMatrix
  let eProd : Fin 1 × Fin n ≃ Fin n :=
    finProdFinEquiv.trans (finCongr (show 1 * n = n by simp))
  eTensor.trans <| eKronecker.trans <| eCoeff.trans <| Matrix.reindexAlgEquiv K K eProd

end CSA

/-- A matrix splitting over `L` extends to a matrix splitting over a field above `L`. -/
private lemma matrix_split_witness_of_isScalarTower
    {L : Type*} {K : Type*} [Field L] [Field K] [Algebra k L] [Algebra k K]
    [Algebra L K] [IsScalarTower k L K] {n : ℕ}
    (e : (A ⊗[k] L) ≃ₐ[L] Matrix (Fin n) (Fin n) L) :
    Nonempty ((A ⊗[k] K) ≃ₐ[K] Matrix (Fin n) (Fin n) K) := by
  let e1 : L ⊗[k] A ≃ₐ[L] Matrix (Fin n) (Fin n) L :=
    (Algebra.TensorProduct.commRight k L A).trans e
  let eTensor : K ⊗[L] (L ⊗[k] A) ≃ₐ[K] K ⊗[L] Matrix (Fin n) (Fin n) L :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) e1
  let eK : K ⊗[k] A ≃ₐ[K] Matrix (Fin n) (Fin n) K :=
    (CSA.cancelBaseChangeAlgEquiv (k := k) (B := A) L K).symm.trans
      (eTensor.trans (CSA.matrix_baseChange_algEquiv (k := k) (L := L) (K := K) n))
  exact ⟨(Algebra.TensorProduct.commRight k K A).symm.trans eK⟩

end

-- ============================================================
-- Owner-level companion statements on CSA
-- ============================================================

namespace CSA

variable {k : Type u} [Field k]
variable (A : CSA.{u, v} k)

private theorem normalClosure_isGalois {L : Type w} [Field L] [Algebra k L]
    [Algebra.IsSeparable k L] :
    IsGalois k (IntermediateField.normalClosure k L (AlgebraicClosure L)) := by
  simpa using
    (IntermediateField.normalClosure.isGalois_of_isSeparable
      (F := k) (E := L) (K := AlgebraicClosure L))

private theorem finite_separable_splitting_field_to_separableClosure :
    ∃ (L : Type v) (_ : Field L) (_ : Algebra k L) (_ : FiniteDimensional k L)
      (_ : Algebra.IsSeparable k L) (_ : Algebra L (SeparableClosure k))
      (_ : IsScalarTower k L (SeparableClosure k)),
      A.IsSplitBy L := by
  rcases A.exists_finite_separable_splitting_field with ⟨L, _, _, _, hLsep, hLsplit⟩
  letI : Algebra.IsAlgebraic k L := Algebra.IsAlgebraic.of_finite k L
  let ι : L →ₐ[k] AlgebraicClosure k := IsAlgClosed.lift
  have hRange : ι.fieldRange ≤ separableClosure k (AlgebraicClosure k) := by
    refine (le_separableClosure_iff k (AlgebraicClosure k) ι.fieldRange).2 ?_
    exact AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField ι)
  let ιsep : L →ₐ[k] SeparableClosure k :=
    ι.codRestrict (separableClosure k (AlgebraicClosure k)).toSubalgebra fun x ↦
      hRange ⟨x, rfl⟩
  letI : Algebra L (SeparableClosure k) := ιsep.toAlgebra
  letI : IsScalarTower k L (SeparableClosure k) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (ιsep.commutes r).symm
  exact ⟨L, inferInstance, inferInstance, inferInstance, hLsep, inferInstance, inferInstance,
    hLsplit⟩

/-- Every finite central simple `k`-algebra splits over `AlgebraicClosure k`. -/
theorem isSplitBy_algebraicClosure : A.IsSplitBy (AlgebraicClosure k) := by
  obtain ⟨n, _, ⟨e⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed (AlgebraicClosure k)
      (A.baseChange (AlgebraicClosure k))
  exact ⟨n, ⟨e⟩⟩

/-- Splitness ascends along a tower of field extensions. -/
theorem isSplitBy_of_isScalarTower
    {L : Type*} {K : Type*} [Field L] [Field K] [Algebra k L] [Algebra k K]
    [Algebra L K] [IsScalarTower k L K] (hL : A.IsSplitBy L) :
    A.IsSplitBy K := by
  rcases hL with ⟨n, ⟨e⟩⟩
  refine ⟨n, ?_⟩
  let eTensor :
      K ⊗[L] (L ⊗[k] A) ≃ₐ[K] K ⊗[L] Matrix (Fin n) (Fin n) L :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) e
  exact ⟨(cancelBaseChangeAlgEquiv (k := k) (B := A) L K).symm.trans <|
    eTensor.trans <| matrix_baseChange_algEquiv (k := k) (L := L) (K := K) n⟩

/-- Every finite central simple `k`-algebra splits over `SeparableClosure k`. -/
theorem isSplitBy_separableClosure : A.IsSplitBy (SeparableClosure k) := by
  rcases A.finite_separable_splitting_field_to_separableClosure with
    ⟨L, _, _, _, _, _, _, hL⟩
  exact A.isSplitBy_of_isScalarTower (L := L) hL

/-- Every finite central simple `k`-algebra admits a finite Galois splitting field. -/
theorem exists_finite_galois_splitting_field :
    ∃ (k' : Type v) (_ : Field k') (_ : Algebra k k') (_ : FiniteDimensional k k')
      (_ : IsGalois k k'),
      A.IsSplitBy k' := by
  rcases A.exists_finite_separable_splitting_field with ⟨L, _, _, _, _, hL⟩
  refine ⟨IntermediateField.normalClosure k L (AlgebraicClosure L), inferInstance, inferInstance,
    inferInstance, ?_,
    ?_⟩
  · exact normalClosure_isGalois (k := k) (L := L)
  · exact A.isSplitBy_of_isScalarTower (L := L) hL

/-- Every finite central simple `k`-algebra admits a finite separable splitting field
in the universe of the algebra itself. -/
theorem exists_finite_separable_splitting_field_galois :
    ∃ (L : Type v) (_ : Field L) (_ : Algebra k L) (_ : FiniteDimensional k L)
      (_ : Algebra.IsSeparable k L),
      A.IsSplitBy L := by
  exact A.exists_finite_separable_splitting_field

end CSA

-- ============================================================
-- The main TFAE theorem
-- ============================================================

section

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]

-- Local instance justification (noncanonical choice): select the right extension-field action; global registration conflicts with the left action when the tensor factors coincide.
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- For a `k`-algebra `A`, finite-dimensionality, centrality, and simplicity are equivalent to
the center being exactly `k` with only trivial two-sided ideals, splitting over the algebraic or
separable closure, splitting over a finite Galois extension of `k`, and being a full matrix
algebra over a finite central division `k`-algebra. -/
theorem CSA.splitting_tfae :
    List.TFAE
      [ FiniteDimensional k A ∧ Algebra.IsCentral k A ∧ IsSimpleRing A,
        FiniteDimensional k A ∧ Subalgebra.center k A = ⊥ ∧
          Nontrivial A ∧ ∀ I : Ideal A, I.IsTwoSided → I = ⊥ ∨ I = ⊤,
        ∃ n : ℕ, n ≠ 0 ∧ Nonempty
          ((A ⊗[k] AlgebraicClosure k) ≃ₐ[AlgebraicClosure k]
            Matrix (Fin n) (Fin n) (AlgebraicClosure k)),
        ∃ n : ℕ, n ≠ 0 ∧ Nonempty
          ((A ⊗[k] SeparableClosure k) ≃ₐ[SeparableClosure k]
            Matrix (Fin n) (Fin n) (SeparableClosure k)),
        ∃ (k' : Type v) (_ : Field k') (_ : Algebra k k') (_ : FiniteDimensional k k')
      (_ : IsGalois k k') (n : ℕ),
          n ≠ 0 ∧ Nonempty ((A ⊗[k] k') ≃ₐ[k'] Matrix (Fin n) (Fin n) k'),
        ∃ (n : ℕ), n ≠ 0 ∧ ∃ (D : Type v) (_ : DivisionRing D) (_ : Algebra k D)
          (_ : FiniteDimensional k D) (_ : Algebra.IsCentral k D),
          Nonempty (A ≃ₐ[k] Matrix (Fin n) (Fin n) D) ] := by
  tfae_have 1 ↔ 2 :=
    finite_central_simple_iff_center_bot_and_two_sided_ideal_trivial (k := k) (A := A)
  tfae_have 1 ↔ 6 :=
    finite_central_simple_iff_matrix_division_form (k := k) (A := A)
  tfae_have 1 → 4 := by
    rintro ⟨hfinite, hcentral, hsimple⟩
    letI : FiniteDimensional k A := hfinite
    letI : Algebra.IsCentral k A := hcentral
    letI : IsSimpleRing A := hsimple
    let ACSA : CSA.{u, v} k := CSA.mk (AlgCat.of k A)
    have hsplit : ACSA.IsSplitBy (SeparableClosure k) := ACSA.isSplitBy_separableClosure
    rcases (ACSA.isSplitBy_iff_exists_pnat (K := SeparableClosure k)).1 hsplit with
      ⟨n, ⟨e⟩⟩
    exact ⟨n, Nat.ne_of_gt n.2,
      ⟨(Algebra.TensorProduct.commRight k (SeparableClosure k) A).symm.trans e⟩⟩
  tfae_have 4 → 3 := by
    rintro ⟨n, hn, ⟨e⟩⟩
    exact ⟨n, hn, matrix_split_witness_of_isScalarTower (k := k) (A := A)
      (L := SeparableClosure k) (K := AlgebraicClosure k) e⟩
  tfae_have 1 → 5 := by
    rintro ⟨hfinite, hcentral, hsimple⟩
    letI : FiniteDimensional k A := hfinite
    letI : Algebra.IsCentral k A := hcentral
    letI : IsSimpleRing A := hsimple
    let ACSA : CSA.{u, v} k := CSA.mk (AlgCat.of k A)
    rcases ACSA.exists_finite_galois_splitting_field with
      ⟨k', hk'Field, hk'Alg, hk'Finite, hk'Galois, hsplit⟩
    letI : Field k' := hk'Field
    letI : Algebra k k' := hk'Alg
    letI : FiniteDimensional k k' := hk'Finite
    letI : IsGalois k k' := hk'Galois
    rcases (ACSA.isSplitBy_iff_exists_pnat (K := k')).1 hsplit with ⟨n, ⟨e⟩⟩
    exact ⟨k', inferInstance, inferInstance, inferInstance, inferInstance, n,
      Nat.ne_of_gt n.2, ⟨(Algebra.TensorProduct.commRight k k' A).symm.trans e⟩⟩

  tfae_have 5 → 3 := by
    rintro ⟨k', hk'Field, hk'Alg, hk'Finite, hk'Galois, n, hn, ⟨e⟩⟩
    letI : Field k' := hk'Field
    letI : Algebra k k' := hk'Alg
    letI : FiniteDimensional k k' := hk'Finite
    letI : IsGalois k k' := hk'Galois
    letI : Algebra.IsAlgebraic k k' := Algebra.IsAlgebraic.of_finite k k'
    let ι : k' →ₐ[k] AlgebraicClosure k := IsAlgClosed.lift
    letI : Algebra k' (AlgebraicClosure k) := ι.toAlgebra
    letI : IsScalarTower k k' (AlgebraicClosure k) :=
      IsScalarTower.of_algebraMap_eq fun r ↦ (ι.commutes r).symm
    exact ⟨n, hn, matrix_split_witness_of_isScalarTower (k := k) (A := A)
      (L := k') (K := AlgebraicClosure k) e⟩
  tfae_have 3 → 1 := by
    intro hsplit
    have hfinite : FiniteDimensional k A :=
      split_over_algebraicClosure_implies_finiteDimensional (k := k) (A := A) hsplit
    letI : FiniteDimensional k A := hfinite
    have hsimple : IsSimpleRing A :=
      split_over_algebraicClosure_implies_isSimpleRing (k := k) (A := A) hsplit
    letI : IsSimpleRing A := hsimple
    have hcentral : Algebra.IsCentral k A :=
      split_over_algebraicClosure_implies_isCentral (k := k) (A := A) hsplit
    exact ⟨hfinite, hcentral, hsimple⟩
  tfae_finish

end

end
