/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Polynomial.Numerical
import Mathlib.Tactic.CrossRefAttribute

/-!
# Degree bounds for numerical polynomials

@stack 00K3

This leaf owns reusable degree bounds for integer-indexed numerical polynomials.  The witness
degree is natural, so the API follows Mathlib's `Polynomial.degreeLE`/`Polynomial.degreeLT`
convention: `WithBot ℕ` records a non-strict bound and `ℕ` records a strict bound.  In particular,
the bottom bound and strict bound zero both express eventual vanishing.
-/

@[expose] public section

open Filter
open scoped BigOperators

universe u

namespace IsNumericalPolynomial

variable {A : Type u} [AddCommGroup A]

/-- A numerical polynomial function has degree at most `b` when it is eventually zero or has an
eventual binomial-basis witness of degree at most the extended-natural bound `b`. -/
@[stacks 00K3 "numerical-polynomial non-strict degree bound"]
def degreeLE (f : ℤ → A) (b : WithBot ℕ) : Prop :=
  (f =ᶠ[atTop] fun _ ↦ (0 : A)) ∨
    ∃ r : ℕ, (r : WithBot ℕ) ≤ b ∧ IsNumericalPolynomial.hasExpansion f r

/-- A numerical polynomial function has degree strictly below `n` when it is eventually zero or
has an eventual binomial-basis witness of natural degree strictly below `n`. -/
@[stacks 00K3 "numerical-polynomial strict degree bound"]
def degreeLT (f : ℤ → A) (n : ℕ) : Prop :=
  (f =ᶠ[atTop] fun _ ↦ (0 : A)) ∨
    ∃ r : ℕ, r < n ∧ IsNumericalPolynomial.hasExpansion f r

namespace hasExpansion

/-- An expansion whose length is at most `b` supplies a non-strict degree bound. -/
@[stacks 00K3 "expansion gives a non-strict degree bound"]
theorem degreeLE {f : ℤ → A} {r : ℕ} {b : WithBot ℕ}
    (hf : IsNumericalPolynomial.hasExpansion f r) (hr : (r : WithBot ℕ) ≤ b) :
    IsNumericalPolynomial.degreeLE f b :=
  Or.inr ⟨r, hr, hf⟩

/-- An expansion shorter than `n` supplies a strict degree bound. -/
@[stacks 00K3 "expansion gives a strict degree bound"]
theorem degreeLT {f : ℤ → A} {r n : ℕ}
    (hf : IsNumericalPolynomial.hasExpansion f r) (hr : r < n) :
    IsNumericalPolynomial.degreeLT f n :=
  Or.inr ⟨r, hr, hf⟩

end hasExpansion

/-- Eventual vanishing supplies every non-strict degree bound. -/
@[stacks 00K3 "eventual vanishing gives a non-strict degree bound"]
theorem degreeLE.of_eventuallyEq_zero {f : ℤ → A} {b : WithBot ℕ}
    (hf : f =ᶠ[atTop] fun _ ↦ (0 : A)) : degreeLE f b :=
  Or.inl hf

/-- Eventual vanishing supplies every strict degree bound. -/
@[stacks 00K3 "eventual vanishing gives a strict degree bound"]
theorem degreeLT.of_eventuallyEq_zero {f : ℤ → A} {n : ℕ}
    (hf : f =ᶠ[atTop] fun _ ↦ (0 : A)) : degreeLT f n :=
  Or.inl hf

/-- A non-strict bottom degree bound is exactly eventual vanishing. -/
@[simp, stacks 00K3 "bottom numerical-polynomial degree bound"]
theorem degreeLE_bot_iff {f : ℤ → A} :
    degreeLE f ⊥ ↔ f =ᶠ[atTop] fun _ ↦ (0 : A) := by
  simp [degreeLE]

/-- Degree strictly below zero is exactly eventual vanishing. -/
@[simp, stacks 00K3 "zero strict degree bound"]
theorem degreeLT_zero_iff {f : ℤ → A} :
    degreeLT f 0 ↔ f =ᶠ[atTop] fun _ ↦ (0 : A) := by
  simp [degreeLT]

/-- A strict bound below `n + 1` is the same as a non-strict bound by `n`. -/
@[stacks 00K3 "strict and non-strict degree bounds"]
theorem degreeLT_succ_iff_degreeLE {f : ℤ → A} (n : ℕ) :
    degreeLT f (n + 1) ↔ degreeLE f n := by
  simp [degreeLT, degreeLE]

/-- A non-strict degree bound is stronger than numerical-polynomiality. -/
@[stacks 00K3 "forget a non-strict degree bound"]
theorem degreeLE.isNumericalPolynomial
    {f : ℤ → A} {b : WithBot ℕ} (hf : degreeLE f b) :
    IsNumericalPolynomial f := by
  rcases hf with hzero | ⟨r, _, hr⟩
  · exact IsNumericalPolynomial.of_eventuallyEq_zero hzero
  · exact hr.isNumericalPolynomial

/-- A strict degree bound is stronger than numerical-polynomiality. -/
@[stacks 00K3 "forget a strict degree bound"]
theorem degreeLT.isNumericalPolynomial
    {f : ℤ → A} {n : ℕ} (hf : degreeLT f n) :
    IsNumericalPolynomial f := by
  rcases hf with hzero | ⟨r, _, hr⟩
  · exact IsNumericalPolynomial.of_eventuallyEq_zero hzero
  · exact hr.isNumericalPolynomial

/-- A larger extended-natural bound preserves a non-strict numerical-polynomial degree bound. -/
@[stacks 00K3 "monotonicity of non-strict degree bounds"]
theorem degreeLE.mono {f : ℤ → A} {b c : WithBot ℕ}
    (h : degreeLE f b) (hbc : b ≤ c) : degreeLE f c := by
  rcases h with hzero | ⟨r, hr, hExpansion⟩
  · exact Or.inl hzero
  · exact Or.inr ⟨r, hr.trans hbc, hExpansion⟩

/-- A larger natural bound preserves a strict numerical-polynomial degree bound. -/
@[stacks 00K3 "monotonicity of strict degree bounds"]
theorem degreeLT.mono {f : ℤ → A} {m n : ℕ}
    (h : degreeLT f m) (hmn : m ≤ n) : degreeLT f n := by
  rcases h with hzero | ⟨r, hr, hExpansion⟩
  · exact Or.inl hzero
  · exact Or.inr ⟨r, hr.trans_le hmn, hExpansion⟩

/-- Eventual equality preserves a non-strict numerical-polynomial degree bound. -/
@[stacks 00K3 "eventual equality and non-strict degree"]
theorem degreeLE.congr {f g : ℤ → A} {b : WithBot ℕ}
    (hf : degreeLE f b) (hfg : f =ᶠ[atTop] g) : degreeLE g b := by
  rcases hf with hzero | ⟨r, hr, hExpansion⟩
  · exact Or.inl (hfg.symm.trans hzero)
  · exact Or.inr ⟨r, hr, hExpansion.congr hfg⟩

/-- Eventual equality preserves a strict numerical-polynomial degree bound. -/
@[stacks 00K3 "eventual equality and strict degree"]
theorem degreeLT.congr {f g : ℤ → A} {n : ℕ}
    (hf : degreeLT f n) (hfg : f =ᶠ[atTop] g) : degreeLT g n := by
  rcases hf with hzero | ⟨r, hr, hExpansion⟩
  · exact Or.inl (hfg.symm.trans hzero)
  · exact Or.inr ⟨r, hr, hExpansion.congr hfg⟩

namespace degreeLT

private theorem multichoose_sub_of_pos (d e : ℕ) (_hd : 1 < d) (_he : 0 < e) :
    IsNumericalPolynomial.degreeLT
      (fun n : ℤ ↦ (d.multichoose n.toNat : ℤ) -
        (d.multichoose (n.toNat - e) : ℤ)) (d - 1) := sorry

/-- A fixed finite difference of a multichoose function has degree strictly
below the degree of the original multichoose function. -/
@[stacks 00K3 "degree of a multichoose finite difference"]
theorem multichoose_sub (d e : ℕ) :
    IsNumericalPolynomial.degreeLT
      (fun n : ℤ ↦ (d.multichoose n.toNat : ℤ) -
        (d.multichoose (n.toNat - e) : ℤ)) (d - 1) := by
  by_cases he : e = 0
  · subst e
    left
    filter_upwards [] with n
    simp
  by_cases hd0 : d = 0
  · subst d
    left
    filter_upwards [eventually_ge_atTop (e + 1 : ℤ)] with n hn
    have hnpos : 0 < n.toNat := by omega
    have hsubpos : 0 < n.toNat - e := by omega
    obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
    obtain ⟨b, hb⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hsubpos)
    rw [hb, ha, Nat.multichoose_zero_succ, Nat.multichoose_zero_succ]
    simp
  by_cases hd1 : d = 1
  · subst d
    left
    filter_upwards [] with n
    simp only [Nat.multichoose_one, Nat.cast_one, sub_self]
  exact multichoose_sub_of_pos d e (by omega) (by omega)

/-- An eventually nonnegative numerical polynomial bounded above by a
strictly lower-degree numerical polynomial satisfies the same degree bound. -/
private theorem of_eventually_nonneg_le_of_hasExpansion
    {f g : ℤ → ℤ} {n r : ℕ}
    (hf : IsNumericalPolynomial f) (hr : r < n)
    (hg : IsNumericalPolynomial.hasExpansion g r)
    (hfg : ∀ᶠ x : ℤ in atTop, 0 ≤ f x ∧ f x ≤ g x) :
    IsNumericalPolynomial.degreeLT f n := sorry

/-- An eventually nonnegative numerical polynomial bounded above by a
strictly lower-degree numerical polynomial satisfies the same degree bound. -/
@[stacks 00K3 "degree bound from eventual nonnegative domination"]
theorem of_eventually_nonneg_le {f g : ℤ → ℤ} {n : ℕ}
    (hf : IsNumericalPolynomial f) (hg : IsNumericalPolynomial.degreeLT g n)
    (hfg : ∀ᶠ x : ℤ in atTop, 0 ≤ f x ∧ f x ≤ g x) :
    IsNumericalPolynomial.degreeLT f n := by
  rcases hg with hzero | ⟨r, hr, hExpansion⟩
  · left
    filter_upwards [hzero, hfg] with x hxg hx
    rw [hxg] at hx
    omega
  · exact of_eventually_nonneg_le_of_hasExpansion hf hr hExpansion hfg

end degreeLT

end IsNumericalPolynomial
