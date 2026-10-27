/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal

@[expose] public section

universe u

noncomputable section

namespace ZeroDimFlatIdeal

open MvPolynomial

variable (k : Type u)

/-- The two families of variables `X i` and `Y i` in the presentation. -/
inductive Var
  | x : ℕ → Var
  | y : ℕ → Var
  deriving DecidableEq

section

variable [CommRing k]

/-- The ambient polynomial ring `k[X i, Y i]`. -/
abbrev PolynomialRing : Type u := MvPolynomial Var k

/-- The relation `X i - Y i * X (i + 1)`. -/
def xRecurrence (i : ℕ) : PolynomialRing k :=
  X (.x i) - X (.y i) * X (.x (i + 1))

/-- The relation `Y i ^ 2`. -/
def ySquare (i : ℕ) : PolynomialRing k :=
  X (.y i) ^ 2

/-- The two infinite families of defining relations. -/
def relations : Set (PolynomialRing k) :=
  Set.range (xRecurrence k) ∪ Set.range (ySquare k)

/-- The defining ideal `(X i - Y i * X (i + 1), Y i ^ 2)`. -/
def relationIdeal : Ideal (PolynomialRing k) :=
  Ideal.span (relations k)

/-- The quotient ring `k[X i, Y i] ⧸ (X i - Y i * X (i + 1), Y i ^ 2)`. -/
abbrev Ring : Type u := PolynomialRing k ⧸ relationIdeal k

/-- The image of `X i` in the quotient. -/
def x (i : ℕ) : Ring k :=
  Ideal.Quotient.mk (relationIdeal k) (X (.x i))

/-- The image of `Y i` in the quotient. -/
def y (i : ℕ) : Ring k :=
  Ideal.Quotient.mk (relationIdeal k) (X (.y i))

/-- The ideal `m = (x i, y i)`. -/
def maximalIdeal : Ideal (Ring k) :=
  Ideal.span (Set.range (x k) ∪ Set.range (y k))

/-- The ideal `I = (x i)`. -/
def xIdeal : Ideal (Ring k) :=
  Ideal.span (Set.range (x k))

/-- Each recurrence polynomial lies in the defining ideal. -/
theorem xRecurrence_mem_relationIdeal (i : ℕ) :
    xRecurrence k i ∈ relationIdeal k := by
  exact Ideal.subset_span (Or.inl ⟨i, rfl⟩)

/-- Each square polynomial lies in the defining ideal. -/
theorem ySquare_mem_relationIdeal (i : ℕ) :
    ySquare k i ∈ relationIdeal k := by
  exact Ideal.subset_span (Or.inr ⟨i, rfl⟩)

/-- The images satisfy `x i = y i * x (i + 1)`. -/
theorem x_eq_y_mul_x_succ (i : ℕ) : x k i = y k i * x k (i + 1) := by
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr (xRecurrence_mem_relationIdeal k i)
  simpa [xRecurrence, x, y, map_sub, map_mul, sub_eq_zero] using h

/-- The images satisfy `y i ^ 2 = 0`. -/
theorem y_sq (i : ℕ) : y k i ^ 2 = 0 := by
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr (ySquare_mem_relationIdeal k i)
  simpa [ySquare, y, map_pow] using h

/-- Each generator `x i` lies in `I = (x i)`. -/
theorem x_mem_xIdeal (i : ℕ) : x k i ∈ xIdeal k := by
  exact Ideal.subset_span ⟨i, rfl⟩

/-- Each generator `x i` lies in `m = (x i, y i)`. -/
theorem x_mem_maximalIdeal (i : ℕ) : x k i ∈ maximalIdeal k := by
  exact Ideal.subset_span (Or.inl ⟨i, rfl⟩)

/-- Each generator `y i` lies in `m = (x i, y i)`. -/
theorem y_mem_maximalIdeal (i : ℕ) : y k i ∈ maximalIdeal k := by
  exact Ideal.subset_span (Or.inr ⟨i, rfl⟩)

/-- Every prime contains the square-zero `y i`, hence also the `x i`. -/
theorem maximalIdeal_le_of_isPrime {p : Ideal (Ring k)} (hp : p.IsPrime) :
    maximalIdeal k ≤ p := by
  have hy (i : ℕ) : y k i ∈ p := by
    exact hp.mem_of_pow_mem 2 ((y_sq k i).symm ▸ p.zero_mem)
  apply Ideal.span_le.mpr
  rintro a (⟨i, rfl⟩ | ⟨i, rfl⟩)
  · rw [x_eq_y_mul_x_succ]
    exact p.mul_mem_right _ (hy i)
  · exact hy i

/-- A finite collection of recurrence relations cannot kill `x 0`: at a stage `n`,
send `X i` to the squarefree product of `Y i, ..., Y (n - 1)`. -/
theorem x_zero_ne_zero [Nontrivial k] : x k 0 ≠ 0 := by
  classical
  intro hx
  have hxmem := Ideal.Quotient.eq_zero_iff_mem.mp hx
  let I (n : ℕ) : Ideal (PolynomialRing k) :=
    Ideal.span (xRecurrence k '' Set.Iio n ∪ Set.range (ySquare k))
  have hmono : Monotone I := by
    intro n m hnm
    apply Ideal.span_mono
    rintro a (⟨i, hi, rfl⟩ | ha)
    · exact Or.inl ⟨i, lt_of_lt_of_le hi hnm, rfl⟩
    · exact Or.inr ha
  have hrel : relationIdeal k = ⨆ n, I n := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro a (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact (le_iSup I (i + 1))
          (Ideal.subset_span (Or.inl ⟨i, Nat.lt_succ_self i, rfl⟩))
      · exact (le_iSup I 0) (Ideal.subset_span (Or.inr ⟨i, rfl⟩))
    · apply iSup_le
      intro n
      apply Ideal.span_le.mpr
      rintro a (⟨i, hi, rfl⟩ | ⟨i, rfl⟩)
      · exact xRecurrence_mem_relationIdeal k i
      · exact ySquare_mem_relationIdeal k i
  rw [hrel] at hxmem
  obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed I hmono.directed_le).mp hxmem
  let J : Ideal (MvPolynomial ℕ k) :=
    Ideal.span ((fun s => monomial s (1 : k)) ''
      Set.range (fun i : ℕ => Finsupp.single i 2))
  let f : Var → MvPolynomial ℕ k
    | .x i => ∏ j ∈ Finset.Ico i n, X j
    | .y i => X i
  let φ : PolynomialRing k →+* MvPolynomial ℕ k := eval₂Hom C f
  have hmap : I n ≤ J.comap φ := by
    apply Ideal.span_le.mpr
    rintro a (⟨i, hi, rfl⟩ | ⟨i, rfl⟩)
    · change φ (xRecurrence k i) ∈ J
      have hrec : φ (xRecurrence k i) = 0 := by
        simp only [φ, xRecurrence, map_sub, map_mul, eval₂Hom_X', f]
        rw [Finset.prod_eq_prod_Ico_succ_bot hi]
        exact sub_self _
      exact hrec.symm ▸ J.zero_mem
    · change φ (ySquare k i) ∈ J
      simp only [φ, ySquare, map_pow, eval₂Hom_X', f]
      exact Ideal.subset_span ⟨Finsupp.single i 2, ⟨i, rfl⟩,
        by simp [X_pow_eq_monomial]⟩
  have hprod := hmap hn
  change φ (X (.x 0)) ∈ J at hprod
  simp only [φ, eval₂Hom_X', f] at hprod
  let d : ℕ →₀ ℕ := Finsupp.indicator (Finset.range n) (fun _ _ => 1)
  have hprod_eq : (∏ j ∈ Finset.Ico 0 n, (X j : MvPolynomial ℕ k)) =
      monomial d 1 := by
    simpa [d] using (prod_X_pow (R := k) (fun _ : ℕ => 1) (Finset.range n))
  rw [hprod_eq] at hprod
  obtain ⟨s, ⟨i, rfl⟩, hi⟩ := mem_ideal_span_monomial_image.mp hprod d (by simp)
  have hd : d i ≤ 1 := by
    by_cases hi : i < n <;> simp [d, Finsupp.indicator, hi]
  have htwo : 2 ≤ d i := by simpa using hi i
  exact (by decide : ¬ 2 ≤ (1 : ℕ)) (htwo.trans hd)

end

section

variable [Field k]

/-- Killing all the variables gives the coefficient field, so `m` is maximal. -/
theorem maximalIdeal_isMaximal : (maximalIdeal k).IsMaximal := by
  have hrel : relationIdeal k ≤ RingHom.ker (constantCoeff : PolynomialRing k →+* k) := by
    apply Ideal.span_le.mpr
    rintro a (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · simp [RingHom.mem_ker, xRecurrence]
    · simp [RingHom.mem_ker, ySquare]
  let ε : Ring k →+* k := Ideal.Quotient.lift (relationIdeal k) constantCoeff
    (fun _ hp => hrel hp)
  let q : PolynomialRing k →+* Ring k := Ideal.Quotient.mk (relationIdeal k)
  let π : Ring k →+* Ring k ⧸ maximalIdeal k := Ideal.Quotient.mk (maximalIdeal k)
  have heq : π.comp q = ((π.comp q).comp C).comp constantCoeff := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro v
      cases v with
      | x i =>
        simpa [π, q, x] using
          (Ideal.Quotient.eq_zero_iff_mem.mpr (x_mem_maximalIdeal k i))
      | y i =>
        simpa [π, q, y] using
          (Ideal.Quotient.eq_zero_iff_mem.mpr (y_mem_maximalIdeal k i))
  have hker : RingHom.ker ε = maximalIdeal k := by
    apply le_antisymm
    · intro a ha
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
      change constantCoeff p = 0 at ha
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change π (q p) = 0
      calc
        π (q p) = π (q (C (constantCoeff p))) := RingHom.congr_fun heq p
        _ = 0 := by rw [ha]; simp
    · apply Ideal.span_le.mpr
      rintro a (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · simp [RingHom.mem_ker, ε, x]
      · simp [RingHom.mem_ker, ε, y]
  rw [← hker]
  exact RingHom.ker_isMaximal_of_surjective ε
    (fun c => ⟨q (C c), by simp [ε, q]⟩)

/-- The presented quotient is a local ring. -/
instance instIsLocalRing : IsLocalRing (Ring k) := by
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨maximalIdeal k, maximalIdeal_isMaximal k, ?_⟩
  intro p hp
  exact ((maximalIdeal_isMaximal k).eq_of_le hp.ne_top
    (maximalIdeal_le_of_isPrime k hp.isPrime)).symm

/-- The presented quotient has Krull dimension at most `0`. -/
instance instKrullDimLE : _root_.Ring.KrullDimLE 0 (Ring k) := by
  apply _root_.Ring.KrullDimLE.mk₀
  intro p hp
  have heq := (maximalIdeal_isMaximal k).eq_of_le hp.ne_top
    (maximalIdeal_le_of_isPrime k hp)
  exact heq ▸ maximalIdeal_isMaximal k

/-- The ideal `(x i)` is flat as a module over the presented quotient. -/
instance instFlat_xIdeal : Module.Flat (Ring k) (xIdeal k) := sorry

/-- The ideal `I = (x i)` is nonzero. -/
theorem xIdeal_ne_bot : xIdeal k ≠ ⊥ := by
  intro h
  have hx := x_mem_xIdeal k 0
  rw [h, Ideal.mem_bot] at hx
  exact x_zero_ne_zero k hx

/-- The ideal `I = (x i)` is proper. -/
theorem xIdeal_ne_top : xIdeal k ≠ ⊤ := by
  apply ne_top_of_le_ne_top (maximalIdeal_isMaximal k).ne_top
  exact Ideal.span_le.mpr (by rintro a ⟨i, rfl⟩; exact x_mem_maximalIdeal k i)

/-- The presented quotient has a unique prime ideal. -/
theorem existsUnique_isPrime : ∃! p : Ideal (Ring k), p.IsPrime := by
  refine ⟨maximalIdeal k, (maximalIdeal_isMaximal k).isPrime, ?_⟩
  intro p hp
  exact ((maximalIdeal_isMaximal k).eq_of_le hp.ne_top
    (maximalIdeal_le_of_isPrime k hp)).symm

/-- A prime ideal of the presented quotient is exactly `m = (x i, y i)`. -/
theorem isPrime_iff_eq_maximalIdeal {p : Ideal (Ring k)} :
    p.IsPrime ↔ p = maximalIdeal k := by
  constructor
  · intro hp
    exact (existsUnique_isPrime k).unique hp (maximalIdeal_isMaximal k).isPrime
  · rintro rfl
    exact (maximalIdeal_isMaximal k).isPrime

end

end ZeroDimFlatIdeal

/-- There exists a commutative local ring with a unique prime ideal and a nonzero
proper ideal that is flat as a module over the ring. -/
theorem exists_isLocalRing_uniquePrime_nonzero_flat_ideal :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsLocalRing R) (I : Ideal R),
      (∃! p : Ideal R, p.IsPrime) ∧ I ≠ ⊥ ∧ I ≠ ⊤ ∧ Module.Flat R I := by
  refine ⟨ZeroDimFlatIdeal.Ring (ULift.{u} ℚ), inferInstance, inferInstance,
    ZeroDimFlatIdeal.xIdeal (ULift.{u} ℚ), ?_⟩
  exact ⟨ZeroDimFlatIdeal.existsUnique_isPrime _, ZeroDimFlatIdeal.xIdeal_ne_bot _,
    ZeroDimFlatIdeal.xIdeal_ne_top _, inferInstance⟩
