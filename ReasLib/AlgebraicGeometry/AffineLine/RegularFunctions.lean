/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Data.Real.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import ReasLib.AlgebraicGeometry.AffineSpace.RegularFunctions

/-!
# Classical regular functions on the affine line

Regular functions on a Zariski locally closed subset of the k-points of the affine line,
in the classical sense.
-/

@[expose] public section

noncomputable section

universe u

namespace Polynomial

variable {k : Type u} [Field k]

/-- A subset of the affine line is Zariski locally closed when it is the difference of
zero loci of nested ideals. -/
def IsZariskiLocallyClosed (Z : Set k) : Prop :=
  ∃ I J : Ideal (Polynomial k), I ≤ J ∧
    Z = {x | ∀ p ∈ I, p.eval x = 0} \ {x | ∀ p ∈ J, p.eval x = 0}

/-- Zariski locally closed subsets of the affine line are differences of nested zero loci. -/
theorem isZariskiLocallyClosed_iff (Z : Set k) :
    IsZariskiLocallyClosed Z ↔
      ∃ I J : Ideal (Polynomial k), I ≤ J ∧
        Z = {x | ∀ p ∈ I, p.eval x = 0} \ {x | ∀ p ∈ J, p.eval x = 0} :=
  Iff.rfl

/-- The affine line is Zariski locally closed in itself. -/
theorem isZariskiLocallyClosed_univ : IsZariskiLocallyClosed (Set.univ : Set k) :=
  by
    refine ⟨⊥, ⊤, bot_le, ?_⟩
    ext x
    constructor
    · intro _
      constructor
      · intro p hp
        have hp0 : p = 0 := (Ideal.mem_bot.mp hp)
        simpa [hp0]
      · intro hx
        have hx1 : (1 : k) = 0 := by
          simpa using hx (1 : Polynomial k) (by simp)
        exact one_ne_zero hx1
    · intro _
      trivial

/-- A relative Zariski open of `Z ⊆ k` is the complement in `Z` of a zero locus. -/
def IsZariskiOpenIn (U Z : Set k) : Prop :=
  U ⊆ Z ∧ ∃ I : Ideal (Polynomial k), U = Z \ {x | ∀ p ∈ I, p.eval x = 0}

/-- Relative Zariski opens on the affine line are complements of zero loci inside `Z`. -/
theorem isZariskiOpenIn_iff (U Z : Set k) :
    IsZariskiOpenIn U Z ↔
      U ⊆ Z ∧ ∃ I : Ideal (Polynomial k), U = Z \ {x | ∀ p ∈ I, p.eval x = 0} :=
  Iff.rfl

/-- A function on a subset of the affine line is regular if it is Zariski-locally a ratio of
polynomials with nonvanishing denominator. -/
def IsRegular {Z : Set k} (φ : Z → k) : Prop :=
  ∀ z : Z, ∃ U : Set k, IsZariskiOpenIn U Z ∧ z.val ∈ U ∧
    ∃ f g : Polynomial k,
      (∀ u ∈ U, g.eval u ≠ 0) ∧
      (∀ u : Z, u.val ∈ U → φ u = f.eval u.val / g.eval u.val)

/-- Regularity on the affine line is the existence of local polynomial ratios. -/
theorem isRegular_iff {Z : Set k} (φ : Z → k) :
    IsRegular φ ↔
      ∀ z : Z, ∃ U : Set k, IsZariskiOpenIn U Z ∧ z.val ∈ U ∧
        ∃ f g : Polynomial k,
          (∀ u ∈ U, g.eval u ≠ 0) ∧
          (∀ u : Z, u.val ∈ U → φ u = f.eval u.val / g.eval u.val) :=
  Iff.rfl

/-- A function on a subset of the affine line is polynomial if it is given by evaluation of a
univariate polynomial. -/
def IsPolynomial {Z : Set k} (φ : Z → k) : Prop :=
  ∃ p : Polynomial k, ∀ z : Z, φ z = p.eval z.val

/-- Polynomial functions on the affine line are those given by a univariate polynomial. -/
theorem isPolynomial_iff {Z : Set k} (φ : Z → k) :
    IsPolynomial φ ↔ ∃ p : Polynomial k, ∀ z : Z, φ z = p.eval z.val :=
  Iff.rfl

private theorem zeroSet_span_singleton (r : Polynomial k) :
    {x : k | ∀ p ∈ (Ideal.span ({r} : Set (Polynomial k))), p.eval x = 0} =
      {x : k | r.eval x = 0} := by
  ext x
  constructor
  · intro hx
    exact hx r (Ideal.mem_span_singleton_self r)
  · intro hx p hp
    rcases Ideal.mem_span_singleton'.mp hp with ⟨a, ha⟩
    rw [← ha, eval_mul, hx, mul_zero]

private theorem isZariskiOpenIn_compl_eval (Z : Set k) (r : Polynomial k) :
    IsZariskiOpenIn (Z \ {x : k | r.eval x = 0}) Z := by
  refine ⟨Set.sdiff_subset, ⟨Ideal.span ({r} : Set (Polynomial k)), ?_⟩⟩
  rw [zeroSet_span_singleton]

private theorem eval_unique_fin1 (q : MvPolynomial (Fin 1) k) (x : Fin 1 → k) :
    ((MvPolynomial.uniqueAlgEquiv k (Fin 1)) q).eval (x 0) =
      MvPolynomial.eval x q := by
  change Polynomial.eval₂ (RingHom.id k) (x 0) _ =
    MvPolynomial.eval₂ (RingHom.id k) x q
  simpa using (MvPolynomial.eval₂_uniqueAlgEquiv (f := q) (φ := RingHom.id k) (a := x))

private theorem eval_unique_fin1_symm (p : Polynomial k) (x : Fin 1 → k) :
    MvPolynomial.eval x ((MvPolynomial.uniqueAlgEquiv k (Fin 1)).symm p) =
      p.eval (x 0) := by
  change MvPolynomial.eval₂ (RingHom.id k) x _ =
    Polynomial.eval₂ (RingHom.id k) (x 0) p
  simpa using (MvPolynomial.eval₂_uniqueAlgEquiv_symm (f := p) (φ := RingHom.id k) (a := x))

private theorem zeroSet_map_toMvPolynomial (I : Ideal (Polynomial k)) :
    {x : Fin 1 → k | ∀ p ∈ I, p.eval (x 0) = 0} =
      {x : Fin 1 → k |
        ∀ q ∈ Ideal.map (Polynomial.toMvPolynomial (R := k) 0) I,
          MvPolynomial.eval x q = 0} := by
  ext x
  constructor
  · intro hx q hq
    have hle : Ideal.map (Polynomial.toMvPolynomial (R := k) 0) I ≤
        RingHom.ker (MvPolynomial.eval x) := by
      rw [Ideal.map_le_iff_le_comap]
      intro p hp
      change MvPolynomial.eval x (Polynomial.toMvPolynomial (R := k) 0 p) = 0
      simpa only [MvPolynomial.eval_toMvPolynomial] using hx p hp
    exact hle hq
  · intro hx p hp
    have hq := hx (Polynomial.toMvPolynomial (R := k) 0 p)
      (Ideal.mem_map_of_mem (Polynomial.toMvPolynomial (R := k) 0) hp)
    simpa only [MvPolynomial.eval_toMvPolynomial] using hq

private theorem zeroSet_comap_uniqueAlgEquiv (J : Ideal (MvPolynomial (Fin 1) k)) :
    {a : k | ∀ p ∈ Ideal.comap
        ((MvPolynomial.uniqueAlgEquiv k (Fin 1)).symm.toRingEquiv.toRingHom) J,
      p.eval a = 0} =
      {a : k | ∀ q ∈ J, MvPolynomial.eval (fun _ : Fin 1 => a) q = 0} := by
  ext a
  constructor
  · intro hx q hq
    have hq' : (MvPolynomial.uniqueAlgEquiv k (Fin 1)) q ∈
        Ideal.comap ((MvPolynomial.uniqueAlgEquiv k (Fin 1)).symm.toRingEquiv.toRingHom) J := by
      change (MvPolynomial.uniqueAlgEquiv k (Fin 1)).symm
          ((MvPolynomial.uniqueAlgEquiv k (Fin 1)) q) ∈ J
      rw [AlgEquiv.symm_apply_apply]
      exact hq
    have hp := hx _ hq'
    exact (eval_unique_fin1 q (fun _ : Fin 1 => a)).symm ▸ hp
  · intro hx p hp
    have hq : (MvPolynomial.uniqueAlgEquiv k (Fin 1)).symm p ∈ J := hp
    have hq' := hx _ hq
    simpa only [eval_unique_fin1_symm] using hq'

/-- Polynomial functions on the affine line are regular. -/
theorem isRegular_of_isPolynomial {Z : Set k} {φ : Z → k}
    (hφ : IsPolynomial φ) : IsRegular φ :=
  by
    rcases hφ with ⟨p, hp⟩
    intro z
    refine ⟨Z, ?_, z.property, p, 1, ?_, ?_⟩
    · refine ⟨subset_rfl, ⟨⊤, ?_⟩⟩
      ext x
      constructor
      · intro hx
        refine ⟨hx, ?_⟩
        intro hzero
        have hzero1 : (1 : k) = 0 := by
          simpa using hzero (1 : Polynomial k) (by simp)
        exact one_ne_zero hzero1
      · intro hx
        exact hx.1
    · intro u hu
      simp
    · intro u hu
      simp [hp u]

/-- Regular functions are closed under pointwise addition. -/
theorem isRegular_add {Z : Set k} {φ ψ : Z → k}
    (hφ : IsRegular φ) (hψ : IsRegular ψ) : IsRegular (φ + ψ) :=
  by
    classical
    intro z
    rcases hφ z with ⟨U, hU, hzU, f, g, hg, hφU⟩
    rcases hψ z with ⟨V, hV, hzV, f', g', hg', hψV⟩
    rcases hU.2 with ⟨I, hIU⟩
    rcases hV.2 with ⟨J, hJV⟩
    rw [hIU] at hzU
    rw [hJV] at hzV
    have hp_exists : ∃ p, p ∈ I ∧ p.eval z.val ≠ 0 := by
      by_contra h
      apply hzU.2
      intro p hp
      by_contra hpz
      exact h ⟨p, hp, hpz⟩
    have hq_exists : ∃ q, q ∈ J ∧ q.eval z.val ≠ 0 := by
      by_contra h
      apply hzV.2
      intro q hq
      by_contra hqz
      exact h ⟨q, hq, hqz⟩
    rcases hp_exists with ⟨p, hpI, hpz⟩
    rcases hq_exists with ⟨q, hqJ, hqz⟩
    refine ⟨Z \ {x : k | (p * q).eval x = 0},
      isZariskiOpenIn_compl_eval Z (p * q), ?_,
      f * g' + f' * g, g * g', ?_, ?_⟩
    · refine ⟨z.property, ?_⟩
      change (p * q).eval z.val ≠ 0
      rw [eval_mul]
      exact mul_ne_zero hpz hqz
    · intro u hu
      have huU : u ∈ U := by
        rw [hIU]
        refine ⟨hu.1, ?_⟩
        intro hzero
        apply hu.2
        change (p * q).eval u = 0
        rw [eval_mul, hzero p hpI, zero_mul]
      have huV : u ∈ V := by
        rw [hJV]
        refine ⟨hu.1, ?_⟩
        intro hzero
        apply hu.2
        change (p * q).eval u = 0
        rw [eval_mul, hzero q hqJ, mul_zero]
      rw [eval_mul]
      exact mul_ne_zero (hg u huU) (hg' u huV)
    · intro u hu
      have huU : u.val ∈ U := by
        rw [hIU]
        refine ⟨hu.1, ?_⟩
        intro hzero
        apply hu.2
        change (p * q).eval u.val = 0
        rw [eval_mul, hzero p hpI, zero_mul]
      have huV : u.val ∈ V := by
        rw [hJV]
        refine ⟨hu.1, ?_⟩
        intro hzero
        apply hu.2
        change (p * q).eval u.val = 0
        rw [eval_mul, hzero q hqJ, mul_zero]
      simp only [Pi.add_apply, hφU u huU, hψV u huV, eval_add, eval_mul]
      field_simp [hg u.val huU, hg' u.val huV]

/-- Regular functions are closed under pointwise multiplication. -/
theorem isRegular_mul {Z : Set k} {φ ψ : Z → k}
    (hφ : IsRegular φ) (hψ : IsRegular ψ) : IsRegular (φ * ψ) :=
  by
    classical
    intro z
    rcases hφ z with ⟨U, hU, hzU, f, g, hg, hφU⟩
    rcases hψ z with ⟨V, hV, hzV, f', g', hg', hψV⟩
    rcases hU.2 with ⟨I, hIU⟩
    rcases hV.2 with ⟨J, hJV⟩
    rw [hIU] at hzU
    rw [hJV] at hzV
    have hp_exists : ∃ p, p ∈ I ∧ p.eval z.val ≠ 0 := by
      by_contra h
      apply hzU.2
      intro p hp
      by_contra hpz
      exact h ⟨p, hp, hpz⟩
    have hq_exists : ∃ q, q ∈ J ∧ q.eval z.val ≠ 0 := by
      by_contra h
      apply hzV.2
      intro q hq
      by_contra hqz
      exact h ⟨q, hq, hqz⟩
    rcases hp_exists with ⟨p, hpI, hpz⟩
    rcases hq_exists with ⟨q, hqJ, hqz⟩
    refine ⟨Z \ {x : k | (p * q).eval x = 0},
      isZariskiOpenIn_compl_eval Z (p * q), ?_,
      f * f', g * g', ?_, ?_⟩
    · refine ⟨z.property, ?_⟩
      change (p * q).eval z.val ≠ 0
      rw [eval_mul]
      exact mul_ne_zero hpz hqz
    · intro u hu
      have huU : u ∈ U := by
        rw [hIU]
        refine ⟨hu.1, ?_⟩
        intro hzero
        apply hu.2
        change (p * q).eval u = 0
        rw [eval_mul, hzero p hpI, zero_mul]
      have huV : u ∈ V := by
        rw [hJV]
        refine ⟨hu.1, ?_⟩
        intro hzero
        apply hu.2
        change (p * q).eval u = 0
        rw [eval_mul, hzero q hqJ, mul_zero]
      rw [eval_mul]
      exact mul_ne_zero (hg u huU) (hg' u huV)
    · intro u hu
      have huU : u.val ∈ U := by
        rw [hIU]
        refine ⟨hu.1, ?_⟩
        intro hzero
        apply hu.2
        change (p * q).eval u.val = 0
        rw [eval_mul, hzero p hpI, zero_mul]
      have huV : u.val ∈ V := by
        rw [hJV]
        refine ⟨hu.1, ?_⟩
        intro hzero
        apply hu.2
        change (p * q).eval u.val = 0
        rw [eval_mul, hzero q hqJ, mul_zero]
      simp only [Pi.mul_apply, hφU u huU, hψV u huV, eval_mul]
      field_simp [hg u.val huU, hg' u.val huV]

/-- Constant functions on the affine line are regular. -/
theorem isRegular_const {Z : Set k} (c : k) :
    IsRegular (algebraMap k (Z → k) c) :=
  by
    apply isRegular_of_isPolynomial
    refine ⟨Polynomial.C c, ?_⟩
    intro z
    simp [Pi.algebraMap_apply]

/-- The algebra of regular functions on a subset of the affine line. -/
def regularFunctions (Z : Set k) : Subalgebra k (Z → k) where
  carrier := {φ | IsRegular φ}
  add_mem' := isRegular_add
  mul_mem' := isRegular_mul
  algebraMap_mem' := isRegular_const

/-- Membership in `regularFunctions Z` on the affine line is regularity. -/
theorem mem_regularFunctions_iff {Z : Set k} {φ : Z → k} :
    φ ∈ regularFunctions Z ↔ IsRegular φ :=
  Iff.rfl

/-- Regularity on the affine line agrees with multivariate regularity in one variable. -/
theorem isRegular_univ_iff_mvPolynomial (φ : k → k) :
    IsRegular (fun z : (Set.univ : Set k) ↦ φ z.val) ↔
      MvPolynomial.IsRegular
        (fun z : (Set.univ : Set (Fin 1 → k)) ↦ φ (z.val 0)) :=
  by
    constructor
    · intro h z
      rcases h ⟨z.val 0, Set.mem_univ _⟩ with ⟨U, hU, hzU, f, g, hg, hφ⟩
      rcases hU.2 with ⟨I, hI⟩
      refine ⟨{x : Fin 1 → k | x 0 ∈ U}, ?_, hzU,
        f.toMvPolynomial 0, g.toMvPolynomial 0, ?_, ?_⟩
      · refine ⟨Set.subset_univ _,
          ⟨Ideal.map (Polynomial.toMvPolynomial (R := k) 0) I, ?_⟩⟩
        ext x
        change x 0 ∈ U ↔ x ∈ Set.univ ∧
          ¬ ∀ q ∈ Ideal.map (Polynomial.toMvPolynomial (R := k) 0) I,
            MvPolynomial.eval x q = 0
        rw [hI]
        have hzero := Set.ext_iff.mp (zeroSet_map_toMvPolynomial I) x
        simpa only [Set.mem_sdiff, Set.mem_univ, Set.mem_setOf_eq, true_and] using
          not_congr hzero
      · intro x hx
        simpa only [MvPolynomial.eval_toMvPolynomial] using hg (x 0) hx
      · intro x hx
        simpa only [MvPolynomial.eval_toMvPolynomial] using
          hφ (⟨x.val 0, Set.mem_univ _⟩ : (Set.univ : Set k)) hx
    · intro h z
      rcases h ⟨fun _ : Fin 1 => z.val, Set.mem_univ _⟩ with
        ⟨U, hU, hzU, f, g, hg, hφ⟩
      rcases hU.2 with ⟨J, hJ⟩
      refine ⟨{a : k | (fun _ : Fin 1 => a) ∈ U}, ?_, hzU,
        (MvPolynomial.uniqueAlgEquiv k (Fin 1)) f,
        (MvPolynomial.uniqueAlgEquiv k (Fin 1)) g, ?_, ?_⟩
      · refine ⟨Set.subset_univ _,
          ⟨Ideal.comap ((MvPolynomial.uniqueAlgEquiv k (Fin 1)).symm.toRingEquiv.toRingHom) J,
            ?_⟩⟩
        ext a
        change (fun _ : Fin 1 => a) ∈ U ↔ a ∈ Set.univ ∧
          ¬ ∀ p ∈ Ideal.comap
            ((MvPolynomial.uniqueAlgEquiv k (Fin 1)).symm.toRingEquiv.toRingHom) J,
              p.eval a = 0
        rw [hJ]
        have hzero := Set.ext_iff.mp (zeroSet_comap_uniqueAlgEquiv J) a
        simpa only [Set.mem_sdiff, Set.mem_univ, MvPolynomial.mem_zeroLocus_iff,
          MvPolynomial.aeval_eq_eval, Set.mem_setOf_eq, true_and] using
            (not_congr hzero).symm
      · intro a ha
        change ((MvPolynomial.uniqueAlgEquiv k (Fin 1)) g).eval
          ((fun _ : Fin 1 => a) 0) ≠ 0
        rw [eval_unique_fin1 g (fun _ : Fin 1 => a)]
        exact hg (fun _ : Fin 1 => a) ha
      · intro a ha
        change φ a.val =
          ((MvPolynomial.uniqueAlgEquiv k (Fin 1)) f).eval ((fun _ : Fin 1 => a.val) 0) /
            ((MvPolynomial.uniqueAlgEquiv k (Fin 1)) g).eval ((fun _ : Fin 1 => a.val) 0)
        rw [eval_unique_fin1 f (fun _ : Fin 1 => a.val),
          eval_unique_fin1 g (fun _ : Fin 1 => a.val)]
        exact hφ (⟨fun _ : Fin 1 => a.val, Set.mem_univ _⟩ :
          (Set.univ : Set (Fin 1 → k))) ha

/-- Polynomiality on the affine line agrees with multivariate polynomiality in one variable. -/
theorem isPolynomial_univ_iff_mvPolynomial (φ : k → k) :
    IsPolynomial (fun z : (Set.univ : Set k) ↦ φ z.val) ↔
      MvPolynomial.IsPolynomial
        (fun z : (Set.univ : Set (Fin 1 → k)) ↦ φ (z.val 0)) :=
  by
    constructor
    · rintro ⟨p, hp⟩
      refine ⟨(MvPolynomial.uniqueAlgEquiv k (Fin 1)).symm p, ?_⟩
      intro z
      calc
        φ (z.val 0) = p.eval (z.val 0) :=
          hp (⟨z.val 0, Set.mem_univ _⟩ : (Set.univ : Set k))
        _ = MvPolynomial.eval z.val ((MvPolynomial.uniqueAlgEquiv k (Fin 1)).symm p) :=
          (eval_unique_fin1_symm p z.val).symm
    · rintro ⟨q, hq⟩
      refine ⟨(MvPolynomial.uniqueAlgEquiv k (Fin 1)) q, ?_⟩
      intro z
      calc
        φ z.val = MvPolynomial.eval (fun _ : Fin 1 => z.val) q :=
          hq (⟨fun _ : Fin 1 => z.val, Set.mem_univ _⟩ : (Set.univ : Set (Fin 1 → k)))
        _ = ((MvPolynomial.uniqueAlgEquiv k (Fin 1)) q).eval z.val :=
          (eval_unique_fin1 q (fun _ : Fin 1 => z.val)).symm

/-- The function `x ↦ (1 + x ^ 2)⁻¹` on the real line. -/
def invOneAddSq : ℝ → ℝ := fun x ↦ (1 + x ^ 2)⁻¹

private theorem isRegular_inv_eval (q : Polynomial k) (hq : ∀ x, q.eval x ≠ 0) :
    IsRegular (fun z : (Set.univ : Set k) => (q.eval z.val)⁻¹) := by
  intro z
  refine ⟨Set.univ \ {x : k | q.eval x = 0},
    isZariskiOpenIn_compl_eval Set.univ q, ⟨z.property, hq z.val⟩, 1, q, ?_, ?_⟩
  · intro u hu
    exact hq u
  · intro u hu
    simp

private theorem not_isPolynomial_inv_eval [Infinite k] (q : Polynomial k)
    (hq : ∀ x, q.eval x ≠ 0) (hdeg : q.natDegree ≠ 0) :
    ¬ IsPolynomial (fun z : (Set.univ : Set k) => (q.eval z.val)⁻¹) := by
  rintro ⟨r, hr⟩
  have hmul : q * r = 1 := by
    apply Polynomial.funext
    intro x
    have hrx : r.eval x = (q.eval x)⁻¹ :=
      (hr (⟨x, Set.mem_univ _⟩ : (Set.univ : Set k))).symm
    rw [eval_mul, hrx, eval_one]
    exact mul_inv_cancel₀ (hq x)
  have hd := natDegree_mul (left_ne_zero_of_mul_eq_one hmul)
    (right_ne_zero_of_mul_eq_one hmul)
  rw [hmul, natDegree_one] at hd
  exact hdeg (Nat.add_eq_zero_iff.mp hd.symm).1

/-- The reciprocal of `1 + x ^ 2` is regular on the real affine line but not polynomial. -/
theorem isRegular_not_isPolynomial_invOneAddSq :
    IsRegular (fun z : (Set.univ : Set ℝ) ↦ invOneAddSq z.val) ∧
      ¬ IsPolynomial (fun z : (Set.univ : Set ℝ) ↦ invOneAddSq z.val) :=
  by
    have hq : ∀ x : ℝ, (X ^ 2 + C 1 : Polynomial ℝ).eval x ≠ 0 := by
      intro x
      simp only [eval_add, eval_pow, eval_X, eval_C]
      exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg x) zero_lt_one)
    have hdeg : (X ^ 2 + C 1 : Polynomial ℝ).natDegree ≠ 0 := by
      rw [natDegree_X_pow_add_C]
      decide
    simpa [invOneAddSq, add_comm] using
      And.intro (isRegular_inv_eval (X ^ 2 + C 1) hq)
        (not_isPolynomial_inv_eval (X ^ 2 + C 1) hq hdeg)

/-- The function `x ↦ (x ^ 2 - p)⁻¹` on the `p`-adic numbers. -/
def invXSqSubNat (p : ℕ) [Fact p.Prime] : ℚ_[p] → ℚ_[p] :=
  fun x ↦ (x ^ 2 - (p : ℚ_[p]))⁻¹

/-- The reciprocal of `x ^ 2 - p` is regular on the p-adic affine line but not polynomial. -/
theorem isRegular_not_isPolynomial_invXSqSubNat (p : ℕ) [Fact p.Prime] :
    IsRegular (fun z : (Set.univ : Set ℚ_[p]) ↦ invXSqSubNat p z.val) ∧
      ¬ IsPolynomial (fun z : (Set.univ : Set ℚ_[p]) ↦ invXSqSubNat p z.val) :=
  by
    have hq : ∀ x : ℚ_[p], (X ^ 2 - C (p : ℚ_[p]) : Polynomial ℚ_[p]).eval x ≠ 0 := by
      intro x hx
      simp only [eval_sub, eval_pow, eval_X, eval_C] at hx
      have hsq : x ^ 2 = (p : ℚ_[p]) := sub_eq_zero.mp hx
      have hv : (2 : ℤ) * x.valuation = 1 := by
        have hv := congrArg Padic.valuation hsq
        simpa only [Padic.valuation_pow, Padic.valuation_p, Nat.cast_ofNat] using hv
      omega
    have hdeg : (X ^ 2 - C (p : ℚ_[p]) : Polynomial ℚ_[p]).natDegree ≠ 0 := by
      rw [natDegree_X_pow_sub_C]
      decide
    simpa [invXSqSubNat] using
      And.intro (isRegular_inv_eval (X ^ 2 - C (p : ℚ_[p])) hq)
        (not_isPolynomial_inv_eval (X ^ 2 - C (p : ℚ_[p])) hq hdeg)

end Polynomial
