/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import ReasLib.Algebra.Module.Graded.NatToInt
public import ReasLib.Algebra.Module.Graded.Hilbert
public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Rank.Domain
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite

/-!
# Weighted polynomial grading and Hilbert function of type (2, 3)

The polynomial ring in two variables with weights `2` and `3` has a locally finite
integer grading. Its Hilbert function counts weighted monomials and does not eventually
agree with a polynomial.
-/

@[expose] public section

noncomputable section

universe u

open MvPolynomial CategoryTheory.ModuleCat GradedModule

namespace MvPolynomial.Weights23

/-- The weight function assigning degree `2` to `x` and degree `3` to `y`. -/
def weight (i : Fin 2) : ℕ :=
  if i = 0 then 2 else 3

/-- Unfolding of the type-`(2, 3)` weight function. -/
theorem weight_apply (i : Fin 2) : weight i = if i = 0 then 2 else 3 := rfl

/-- The first variable has weight `2`. -/
theorem weight_zero : weight 0 = 2 := by decide

/-- The second variable has weight `3`. -/
theorem weight_one : weight 1 = 3 := by decide

variable (k : Type u) [Field k]

/-- The polynomial ring `k[x, y]`, with variables indexed by `Fin 2`. -/
abbrev PolynomialRing :=
  MvPolynomial (Fin 2) k

/-- The weighted homogeneous grading on `k[x, y]` of type `(2, 3)`. -/
abbrev grading : ℕ → Submodule k (PolynomialRing k) :=
  weightedHomogeneousSubmodule k weight

/-- Membership in `grading k n` is weighted homogeneity of degree `n`. -/
theorem mem_grading_iff (n : ℕ) (f : PolynomialRing k) :
    f ∈ grading k n ↔ IsWeightedHomogeneous weight f n := Iff.rfl

/-- The canonical graded-algebra structure on the type-`(2, 3)` weighted polynomial grading. -/
noncomputable instance instGradedAlgebra : GradedAlgebra (grading k) :=
  weightedGradedAlgebra k weight

/-- The integer-indexed grading of `k[x, y]` obtained by extending the natural grading by `⊥`. -/
abbrev integerGrading : ℤ → Submodule k (PolynomialRing k) :=
  DirectSum.Decomposition.natToIntGrading (grading k)

/-- On nonnegative degrees, the integer grading agrees with the natural weighted grading. -/
theorem integerGrading_of_nonneg {n : ℤ} (hn : 0 ≤ n) :
    integerGrading k n = grading k n.toNat := by
  simp only [integerGrading, DirectSum.Decomposition.natToIntGrading, if_pos hn]

/-- On negative degrees, the integer grading is the zero submodule. -/
theorem integerGrading_of_neg {n : ℤ} (hn : n < 0) :
    integerGrading k n = ⊥ := by
  simp only [integerGrading, DirectSum.Decomposition.natToIntGrading, if_neg (not_le.mpr hn)]

/-- Each degree piece of the type-`(2, 3)` integer grading is a finite `k`-module. -/
instance instLocallyFinite : GradedModule.LocallyFinite (integerGrading k) :=
  ⟨fun n ↦ by
    by_cases hn : 0 ≤ n
    · rw [integerGrading_of_nonneg k hn]
      exact Module.Finite.iff_fg.mpr
        (weightedHomogeneousSubmodule_fg (R := k) weight (fun i : Fin 2 ↦ by
          by_cases hi : i = 0 <;> simp [weight, hi]) n.toNat)
    · rw [integerGrading_of_neg k (lt_of_not_ge hn)]
      infer_instance⟩

/-- The Hilbert function of the type-`(2, 3)` weighted polynomial ring is the `k`-dimension
of the degree piece. -/
theorem hilbertFunction_eq_finrank (k : Type u) [Field k] (n : ℤ) :
    hilbertFunction (K0.Finite.genericRank.{u, u} k) (integerGrading k) n =
      Module.finrank k (integerGrading k n) := by
  change K0.Finite.genericRank.{u, u} k
      (K0.finiteOf k (FGModuleCat.of k (integerGrading k n))) = _
  change FreeAbelianGroup.lift (fun M : FGModuleCat.{u} k ↦
      (Module.finrank k M.obj : ℤ)) (FreeAbelianGroup.of
        (FGModuleCat.of k (integerGrading k n))) = _
  exact FreeAbelianGroup.lift_apply_of _ _

/-- In nonnegative degrees, the Hilbert function counts monomials `x^a y^b` of weighted
degree `n`. -/
theorem hilbertFunction_eq_card (k : Type u) [Field k] {n : ℤ} (hn : 0 ≤ n) :
    hilbertFunction (K0.Finite.genericRank.{u, u} k) (integerGrading k) n =
      Nat.card {p : ℕ × ℕ | 2 * p.1 + 3 * p.2 = n.toNat} := by
  classical
  rw [hilbertFunction_eq_finrank, integerGrading_of_nonneg k hn]
  apply congrArg (Nat.cast : ℕ → ℤ)
  change Module.finrank k (weightedHomogeneousSubmodule k weight n.toNat) = _
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported]
  change Module.finrank k
    (restrictSupport k {d | Finsupp.weight weight d = n.toNat}) = _
  rw [Module.finrank_eq_nat_card_basis (basisRestrictSupport k _)]
  apply Nat.card_congr
  exact (Finsupp.equivFunOnFinite.trans (finTwoArrowEquiv ℕ)).subtypeEquiv (fun d ↦ by
    change Finsupp.weight weight d = n.toNat ↔ 2 * d 0 + 3 * d 1 = n.toNat
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]
    simp [weight, mul_comm])

-- Parameterize the solutions by `(3 * j + a, 2 * (q - j) + b)`; the inverse is `p.1 / 3`.
private theorem card_weighted_pairs_of_params (q a b r : ℕ) (ha : a < 3) (hab : 2 * a + 3 * b = r)
    (hmod : ∀ A B : ℕ, 2 * A + 3 * B = 6 * q + r → A % 3 = a)
    (hbase : ∀ A B : ℕ, 2 * A + 3 * B = 6 * q + r → b ≤ B) :
    Nat.card {p : ℕ × ℕ | 2 * p.1 + 3 * p.2 = 6 * q + r} = q + 1 := by
  let f : Fin (q + 1) → {p : ℕ × ℕ | 2 * p.1 + 3 * p.2 = 6 * q + r} := fun j ↦
    ⟨(3 * j.1 + a, 2 * (q - j.1) + b), by
      change 2 * (3 * j.1 + a) + 3 * (2 * (q - j.1) + b) = 6 * q + r
      have hj : j.1 ≤ q := by omega
      omega⟩
  have hbound (p : {p : ℕ × ℕ | 2 * p.1 + 3 * p.2 = 6 * q + r}) : p.1.1 / 3 < q + 1 := by
    rcases p with ⟨⟨A, B⟩, hAB⟩
    change 2 * A + 3 * B = 6 * q + r at hAB
    have hAmod := hmod A B hAB
    have hB := hbase A B hAB
    have hAdiv := Nat.mod_add_div A 3
    rw [hAmod] at hAdiv
    dsimp
    omega
  let e : Fin (q + 1) ≃ {p : ℕ × ℕ | 2 * p.1 + 3 * p.2 = 6 * q + r} :=
    { toFun := f
      invFun := fun p ↦ ⟨p.1.1 / 3, hbound p⟩
      left_inv := by
        intro j
        apply Fin.ext
        change (3 * j.1 + a) / 3 = j.1
        omega
      right_inv := by
        rintro ⟨⟨A, B⟩, hAB⟩
        change 2 * A + 3 * B = 6 * q + r at hAB
        have hAmod := hmod A B hAB
        have hB := hbase A B hAB
        have hAdiv := Nat.mod_add_div A 3
        rw [hAmod] at hAdiv
        apply Subtype.ext
        change (3 * (A / 3) + a, 2 * (q - A / 3) + b) = (A, B)
        apply Prod.ext <;> omega }
  exact (Nat.card_congr e).symm.trans (Nat.card_fin (q + 1))

private theorem card_weighted_pairs (N : ℕ) :
    Nat.card {p : ℕ × ℕ | 2 * p.1 + 3 * p.2 = N} =
      N / 6 + if N % 6 = 1 then 0 else 1 := by
  let q := N / 6
  have hdecomp : N = 6 * q + N % 6 := by dsimp [q]; omega
  have hrlt : N % 6 < 6 := Nat.mod_lt _ (by decide)
  interval_cases hres : N % 6
  · have h := card_weighted_pairs_of_params q 0 0 0 (by decide) (by decide)
        (by intro A B hAB; omega) (by intro A B hAB; omega)
    have hN : N = 6 * q + 0 := by omega
    rw [hN]
    have hdiv : (6 * q + 0) / 6 = q := by omega
    rw [hdiv]
    simpa using h
  · by_cases hq : q = 0
    · letI : IsEmpty {p : ℕ × ℕ | 2 * p.1 + 3 * p.2 = N} := ⟨by
        rintro ⟨⟨a, b⟩, hab⟩
        change 2 * a + 3 * b = N at hab
        omega⟩
      have hc : Nat.card {p : ℕ × ℕ | 2 * p.1 + 3 * p.2 = N} = 0 := by simp
      rw [hc]
      simp only [ite_true, add_zero]
      change 0 = q
      exact hq.symm
    -- In residue class `1`, the first representable degree is `7 = 2 * 2 + 3 * 1`.
    · have h := card_weighted_pairs_of_params (q - 1) 2 1 7 (by decide) (by decide)
        (by intro A B hAB; omega) (by intro A B hAB; omega)
      have hN : N = 6 * (q - 1) + 7 := by omega
      rw [hN]
      have hdiv : (6 * (q - 1) + 7) / 6 = q := by omega
      rw [hdiv]
      have hc : q - 1 + 1 = q := by omega
      simpa [hc] using h
  · have h := card_weighted_pairs_of_params q 1 0 2 (by decide) (by decide)
        (by intro A B hAB; omega) (by intro A B hAB; omega)
    have hN : N = 6 * q + 2 := by omega
    rw [hN]
    have hdiv : (6 * q + 2) / 6 = q := by omega
    rw [hdiv]
    simpa using h
  · have h := card_weighted_pairs_of_params q 0 1 3 (by decide) (by decide)
        (by intro A B hAB; omega) (by intro A B hAB; omega)
    have hN : N = 6 * q + 3 := by omega
    rw [hN]
    have hdiv : (6 * q + 3) / 6 = q := by omega
    rw [hdiv]
    simpa using h
  · have h := card_weighted_pairs_of_params q 2 0 4 (by decide) (by decide)
        (by intro A B hAB; omega) (by intro A B hAB; omega)
    have hN : N = 6 * q + 4 := by omega
    rw [hN]
    have hdiv : (6 * q + 4) / 6 = q := by omega
    rw [hdiv]
    simpa using h
  · have h := card_weighted_pairs_of_params q 1 1 5 (by decide) (by decide)
        (by intro A B hAB; omega) (by intro A B hAB; omega)
    have hN : N = 6 * q + 5 := by omega
    rw [hN]
    have hdiv : (6 * q + 5) / 6 = q := by omega
    rw [hdiv]
    simpa using h

/-- The Hilbert function of `k[x, y]` with weights `2` and `3` is zero in negative degrees
and equals `n / 6 + if n % 6 = 1 then 0 else 1` in nonnegative degrees. -/
theorem hilbertFunction_eq (k : Type u) [Field k] (n : ℤ) :
    hilbertFunction (K0.Finite.genericRank.{u, u} k) (integerGrading k) n =
      if n < 0 then 0 else n / 6 + if n % 6 = 1 then 0 else 1 := by
  by_cases hn : n < 0
  · rw [if_pos hn, hilbertFunction_eq_finrank, integerGrading_of_neg k hn]
    simp
  · have hn0 : 0 ≤ n := le_of_not_gt hn
    rw [if_neg hn, hilbertFunction_eq_card k hn0, card_weighted_pairs]
    have hnNat : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn0
    by_cases hr : n % 6 = 1
    · have hrNat : n.toNat % 6 = 1 := by omega
      rw [if_pos hr, if_pos hrNat]
      simp only [add_zero]
      omega
    · have hrNat : n.toNat % 6 ≠ 1 := by omega
      rw [if_neg hr, if_neg hrNat]
      push_cast
      omega

open Filter in
private theorem no_polynomial_weighted_pairs {P : Polynomial ℚ}
    (hP : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) =
      ((n / 6 + if n % 6 = 1 then 0 else 1 : ℕ) : ℚ)) : False := by
  rcases eventually_atTop.1 hP with ⟨N, hN⟩
  let Q : Polynomial ℚ := Polynomial.C (1 / 6 : ℚ) * Polynomial.X + Polynomial.C 1
  -- Agreement on the infinite progression `6 * q` forces this affine polynomial.
  have hPQ : P = Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    have hinj : Function.Injective (fun q : ℕ ↦ (6 : ℚ) * q) := by
      intro a b hab
      exact Nat.cast_injective (mul_left_cancel₀ (by norm_num : (6 : ℚ) ≠ 0) hab)
    apply ((Set.Ici_infinite N).image hinj.injOn).mono
    rintro x ⟨q, hq, rfl⟩
    have hq' : N ≤ q := hq
    have hpq := hN (6 * q) (by omega)
    simp only [Set.mem_setOf_eq]
    simp only [Q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    norm_num at hpq
    rw [hpq]
    ring
  have hpq := hN (6 * N + 1) (by omega)
  rw [hPQ] at hpq
  have hquot : (6 * N + 1) / 6 = N := by omega
  norm_num [Q] at hpq
  rw [hquot] at hpq
  linarith

private theorem weighted_pairs_expansion_polynomial (r : ℕ) (a : Fin (r + 1) → ℤ) :
    ∃ P : Polynomial ℚ, ∀ n : ℕ, P.eval (n : ℚ) =
      ((∑ i : Fin (r + 1), Ring.choose (n : ℤ) (i : ℕ) • a i : ℤ) : ℚ) := by
  let P : Polynomial ℚ := ∑ i : Fin (r + 1),
    (a i : ℚ) • ((i.val.factorial : ℚ)⁻¹ • descPochhammer ℚ i.val)
  refine ⟨P, ?_⟩
  intro n
  simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_smul, Int.cast_sum, smul_eq_mul,
    Ring.choose_natCast]
  apply Finset.sum_congr rfl
  intro i hi
  push_cast
  rw [Nat.cast_choose_eq_descPochhammer_div]
  ring

open Filter in
/-- The polynomial ring `k[x, y]` with weights `2` and `3` has no Hilbert polynomial
with respect to dimension over `k`. -/
theorem not_hasHilbertPolynomial (k : Type u) [Field k] :
    ¬ HasHilbertPolynomial (K0.Finite.genericRank.{u, u} k) (integerGrading k) := by
  intro h
  rcases h with ⟨r, a, ha⟩
  obtain ⟨P, heval⟩ := weighted_pairs_expansion_polynomial r a
  apply no_polynomial_weighted_pairs (P := P)
  rcases eventually_atTop.1 ha with ⟨N, hN⟩
  filter_upwards [eventually_ge_atTop N.toNat] with n hn
  have hn' : N ≤ (n : ℤ) := by omega
  have heq := hN n hn'
  rw [hilbertFunction_eq] at heq
  have hn0 : ¬ (n : ℤ) < 0 := by omega
  rw [if_neg hn0] at heq
  dsimp only at heq
  rw [heval, ← heq]
  have hc : ((n / 6 + if n % 6 = 1 then 0 else 1 : ℕ) : ℤ) =
      (n : ℤ) / 6 + if (n : ℤ) % 6 = 1 then 0 else 1 := by
    by_cases hmod : n % 6 = 1
    · have hmod' : (n : ℤ) % 6 = 1 := by omega
      rw [if_pos hmod, if_pos hmod']
      simp only [add_zero]
      omega
    · have hmod' : (n : ℤ) % 6 ≠ 1 := by omega
      rw [if_neg hmod, if_neg hmod']
      push_cast
      omega
  rw [← hc]
  norm_cast

end MvPolynomial.Weights23
