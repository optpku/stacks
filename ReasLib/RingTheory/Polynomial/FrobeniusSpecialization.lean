/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.Irreducible.Defs
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.FiniteField
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Frobenius-graph specialization of bivariate polynomials

The constructions in this file specialize a bivariate polynomial along the graph
`Y = X ^ n`, followed by a coefficient homomorphism.
-/

@[expose] public section

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

universe u v

namespace Polynomial

/-- The ring homomorphism `R[X][Y] →+* S[X]` sending `f` to `φ_* f(X, X ^ n)`. -/
def evalXPowRingHom {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (n : ℕ) : R[X][Y] →+* S[X] :=
  (evalRingHom (X ^ n)).comp (mapRingHom (mapRingHom φ))

/-- `evalXPowRingHom φ n` sends a constant-in-`Y` polynomial `C q` to `q.map φ`. -/
theorem evalXPowRingHom_C {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (n : ℕ) (q : R[X]) :
    evalXPowRingHom φ n (C q) = q.map φ := by
  simp [evalXPowRingHom]

/-- `evalXPowRingHom φ n` sends the inner variable `X` to `X`. -/
theorem evalXPowRingHom_X {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (n : ℕ) :
    evalXPowRingHom φ n (C X) = X := by
  simp [evalXPowRingHom_C]

/-- `evalXPowRingHom φ n` sends the outer variable `Y` to `X ^ n`. -/
theorem evalXPowRingHom_Y {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (n : ℕ) :
    evalXPowRingHom φ n Y = X ^ n := by
  simp [evalXPowRingHom]

/-- The specialization `f_p(x) = f(x, x ^ p) mod p` in `(ZMod p)[X]`. -/
def intEvalXPowMod (p : ℕ) (f : ℤ[X][Y]) : (ZMod p)[X] :=
  evalXPowRingHom (Int.castRingHom (ZMod p)) p f

/-- The specialization `intEvalXPowMod p f` is evaluation along the Frobenius graph
followed by reduction of integer coefficients modulo `p`. -/
theorem intEvalXPowMod_spec (p : ℕ) (f : ℤ[X][Y]) :
    intEvalXPowMod p f = evalXPowRingHom (Int.castRingHom (ZMod p)) p f := rfl

/-- The integer bivariate polynomial `Y - C (X + 1)`. -/
def ySubXSucc : ℤ[X][Y] := Y - C (X + 1)

/-- The integer bivariate polynomial `Y ^ 2 - C (X ^ 2) + 1`. -/
def ySqSubXSqAddOne : ℤ[X][Y] := Y ^ 2 - C (X ^ 2) + 1

/-- Frobenius specialization of `Y - C (X + 1)` gives `X ^ p - X - 1`. -/
theorem intEvalXPowMod_ySubXSucc (p : ℕ) :
    intEvalXPowMod p ySubXSucc = X ^ p - X - 1 := by
  simp [intEvalXPowMod, ySubXSucc, map_sub, evalXPowRingHom_Y,
    evalXPowRingHom_C, sub_add_eq_sub_sub]

/-- Frobenius specialization of `Y ^ 2 - C (X ^ 2) + 1` gives
`X ^ (2 * p) - X ^ 2 + 1`. -/
theorem intEvalXPowMod_ySqSubXSqAddOne (p : ℕ) :
    intEvalXPowMod p ySqSubXSqAddOne = X ^ (2 * p) - X ^ 2 + 1 := by
  simp [intEvalXPowMod, ySqSubXSqAddOne, map_add, map_sub, map_pow,
    evalXPowRingHom_Y, evalXPowRingHom_C, ← pow_mul, Nat.mul_comm]

/-- A nonzero translation gives an irreducible Artin–Schreier polynomial over `ZMod p`. -/
private theorem irreducible_X_pow_sub_X_sub_C_zmod (p : ℕ) [Fact p.Prime] (a : ZMod p) (ha : a ≠ 0) :
    Irreducible (X ^ p - X - C a : (ZMod p)[X]) := by
  classical
  have hp := (Fact.out : p.Prime)
  have hsmall : (X + C a : (ZMod p)[X]).degree < p := by
    simpa using (WithBot.coe_lt_coe.mpr hp.one_lt : (1 : WithBot ℕ) < p)
  have hm : (X ^ p - X - C a : (ZMod p)[X]).Monic := by
    simpa [sub_add_eq_sub_sub] using monic_X_pow_sub hsmall
  have hd : (X ^ p - X - C a : (ZMod p)[X]).natDegree = p := by
    rw [natDegree_sub_eq_left_of_natDegree_lt, natDegree_sub_eq_left_of_natDegree_lt]
    · simp
    · simpa using hp.one_lt
    · simp only [natDegree_C]
      rw [natDegree_sub_eq_left_of_natDegree_lt (by simpa using hp.one_lt)]
      simpa using hp.pos
  have hne : (X ^ p - X - C a : (ZMod p)[X]) ≠ 1 := by
    intro h
    have := congrArg natDegree h
    exact hp.ne_zero (by simpa only [hd, natDegree_one] using this)
  apply (hm.irreducible_iff_lt_natDegree_lt hne).mpr
  intro g hg hgdeg hdiv
  rw [hd, Finset.mem_Ioc] at hgdeg
  let b := AdjoinRoot.powerBasisAux' hg
  let z := AdjoinRoot.root g
  have hroot : z ^ p - z - algebraMap (ZMod p) (AdjoinRoot g) a = 0 := by
    have h := _root_.map_dvd (aeval z) hdiv
    have hgroot : aeval z g = 0 := by
      exact AdjoinRoot.eval₂_root g
    rw [hgroot, zero_dvd_iff] at h
    simpa using h
  let M := Algebra.leftMulMatrix b z
  have hM : M ^ p - M - algebraMap (ZMod p) (Matrix (Fin g.natDegree) (Fin g.natDegree) (ZMod p)) a = 0 := by
    simpa only [map_sub, map_pow, AlgHom.commutes, map_zero] using
      congrArg (Algebra.leftMulMatrix b) hroot
  have ht := congrArg Matrix.trace hM
  simp only [Matrix.trace_sub, ZMod.trace_pow_card, ZMod.pow_card,
    sub_self, Algebra.algebraMap_eq_smul_one, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, Matrix.trace_zero, zero_sub, neg_eq_zero, smul_eq_mul] at ht
  have hcast : (g.natDegree : ZMod p) = 0 := by
    exact (mul_eq_zero.mp ht).resolve_left ha
  have hpdvd := (ZMod.natCast_eq_zero_iff _ _).mp hcast
  have hle := Nat.le_of_dvd hgdeg.1 hpdvd
  omega

/-- Some integer bivariate polynomial has irreducible Frobenius specializations
over `ZMod p` for infinitely many primes `p`. -/
theorem exists_intEvalXPowMod_irreducible_infinite :
    ∃ f : ℤ[X][Y], {p : ℕ | p.Prime ∧ Irreducible (intEvalXPowMod p f)}.Infinite := by
  refine ⟨C X, Nat.infinite_setOf_prime.mono ?_⟩
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  exact ⟨hp, by simpa [intEvalXPowMod, evalXPowRingHom_X] using
    (irreducible_X : Irreducible (X : (ZMod p)[X]))⟩

/-- The polynomial `Y - C (X + 1)` has irreducible Frobenius specializations
over `ZMod p` for infinitely many primes `p`. -/
theorem ySubXSucc_intEvalXPowMod_irreducible_infinite :
    {p : ℕ | p.Prime ∧ Irreducible (intEvalXPowMod p ySubXSucc)}.Infinite := by
  apply Nat.infinite_setOf_prime.mono
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  refine ⟨hp, ?_⟩
  simpa [intEvalXPowMod_ySubXSucc] using
    irreducible_X_pow_sub_X_sub_C_zmod p 1 one_ne_zero

/-- The polynomial `Y ^ 2 - C (X ^ 2) + 1` has irreducible Frobenius
specializations over `ZMod p` for infinitely many primes `p`. -/
theorem ySqSubXSqAddOne_intEvalXPowMod_irreducible_infinite :
    {p : ℕ | p.Prime ∧ Irreducible (intEvalXPowMod p ySqSubXSqAddOne)}.Infinite := by
  have hirr (p : ℕ) [Fact p.Prime] (hp3 : p % 4 = 3) :
      Irreducible (X ^ (2 * p) - X ^ 2 + 1 : (ZMod p)[X]) := by
    classical
    let F : (ZMod p)[X] := X ^ p - X - C (-1)
    have hp := (Fact.out : p.Prime)
    have hsmall : (X + C (-1) : (ZMod p)[X]).degree < p := by
      rw [degree_X_add_C]
      exact WithBot.coe_lt_coe.mpr hp.one_lt
    have hm : F.Monic := by
      simpa [F, sub_add_eq_sub_sub] using monic_X_pow_sub hsmall
    have hirr : Irreducible F := irreducible_X_pow_sub_X_sub_C_zmod p (-1) (neg_ne_zero.mpr one_ne_zero)
    have hd : F.natDegree = p := by
      change (X ^ p - X - C (-1) : (ZMod p)[X]).natDegree = p
      rw [natDegree_sub_eq_left_of_natDegree_lt, natDegree_sub_eq_left_of_natDegree_lt]
      · simp
      · simpa using hp.one_lt
      · simp only [natDegree_C]
        rw [natDegree_sub_eq_left_of_natDegree_lt (by simpa using hp.one_lt)]
        simpa using hp.pos
    have hcomp : Irreducible (F.comp (X ^ 2)) := by
      apply irreducible_comp hm (monic_X_pow 2) hirr
      intro E _ _ x hx
      simp only [Polynomial.map_pow, map_X]
      apply (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two).mpr
      intro y hy
      have hxint : IsIntegral (ZMod p) x :=
        minpoly.ne_zero_iff.mp (by rw [hx]; exact hirr.ne_zero)
      let pb := IntermediateField.adjoin.powerBasis hxint
      have hn : Algebra.norm (ZMod p) (IntermediateField.AdjoinSimple.gen (ZMod p) x) = -1 := by
        have hn := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb
        have hpodd : Odd p := Nat.odd_iff.mpr (by omega)
        simp only [pb, IntermediateField.adjoin.powerBasis_gen,
          IntermediateField.adjoin.powerBasis_dim, IntermediateField.minpoly_gen, hx,
          hd] at hn
        simpa [F, hp.ne_zero, Ne.symm hp.ne_zero, hpodd.neg_one_pow] using hn
      have hs : Algebra.norm (ZMod p) y ^ 2 = -1 := by
        rw [← map_pow, hy, hn]
      exact ZMod.mod_four_ne_three_of_sq_eq_neg_one hs hp3
    simpa [F, ← pow_mul, Nat.mul_comm] using hcomp
  have hinf := Nat.infinite_setOf_prime_and_modEq (q := 4) (a := 3)
    (by decide) (by decide)
  apply hinf.mono
  intro p hp
  letI : Fact p.Prime := ⟨hp.1⟩
  refine ⟨hp.1, ?_⟩
  have hp3 : p % 4 = 3 := by simpa [Nat.ModEq] using hp.2
  rw [intEvalXPowMod_ySqSubXSqAddOne]
  exact hirr p hp3

/-- For every nonzero integer bivariate polynomial, the degree of its Frobenius
specialization is eventually `f.natDegree * p + f.leadingCoeff.natDegree` at primes. -/
theorem natDegree_intEvalXPowMod {f : ℤ[X][Y]} (hf : f ≠ 0) :
    ∃ N : ℕ, ∀ p : ℕ, p.Prime → N ≤ p →
      (intEvalXPowMod p f).natDegree = f.natDegree * p + f.leadingCoeff.natDegree := by
  classical
  let M := (Finset.range (f.natDegree + 1)).sup fun i => (f.coeff i).natDegree
  let a := f.leadingCoeff.leadingCoeff
  refine ⟨max (M + 1) (a.natAbs + 1), ?_⟩
  intro p hp hN
  letI : Fact p.Prime := ⟨hp⟩
  have hM : M < p := lt_of_lt_of_le (Nat.lt_succ_self M) ((le_max_left _ _).trans hN)
  have ha : a.natAbs < p :=
    lt_of_lt_of_le (Nat.lt_succ_self _) ((le_max_right _ _).trans hN)
  have ha0 : a ≠ 0 := leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hf)
  have hcast : (a : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ a.natAbs :=
      Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h)
    exact (not_le_of_gt ha) (Nat.le_of_dvd (Int.natAbs_pos.mpr ha0) hdvd)
  let φ := Int.castRingHom (ZMod p)
  have hlc : (f.leadingCoeff.map φ).natDegree = f.leadingCoeff.natDegree :=
    natDegree_map_of_leadingCoeff_ne_zero φ hcast
  have hne : f.leadingCoeff.map φ ≠ 0 := by
    intro h
    have hc := congrArg (fun q : (ZMod p)[X] => q.coeff f.leadingCoeff.natDegree) h
    exact hcast (by simpa [φ, coeff_map, coeff_natDegree] using hc)
  have hsum : intEvalXPowMod p f =
      ∑ i ∈ Finset.range (f.natDegree + 1), (f.coeff i).map φ * X ^ (p * i) := by
    change (f.map (mapRingHom φ)).eval (X ^ p) = _
    rw [eval_map, eval₂_eq_sum_range]
    simp [pow_mul]
  rw [hsum, Finset.sum_range_succ]
  by_cases hd : f.natDegree = 0
  · have hc : f.coeff 0 = f.leadingCoeff := by rw [leadingCoeff, hd]
    simpa only [hd, Finset.range_zero, Finset.sum_empty, zero_add, Nat.mul_zero,
      Nat.zero_mul, pow_zero, mul_one, hc] using hlc
  · have hlow : (∑ i ∈ Finset.range f.natDegree,
        (f.coeff i).map φ * X ^ (p * i)).natDegree <
        ((f.coeff f.natDegree).map φ * X ^ (p * f.natDegree)).natDegree := by
      rw [coeff_natDegree, natDegree_mul_X_pow _ hne, hlc]
      have hpos : 0 < p * f.natDegree := Nat.mul_pos hp.pos (Nat.pos_of_ne_zero hd)
      apply lt_of_lt_of_le ?_ (Nat.le_add_left _ _)
      refine lt_of_le_of_lt
        (natDegree_sum_le_of_forall_le (n := p * f.natDegree - 1) _ _ ?_)
        (Nat.sub_lt hpos (by decide : 0 < (1 : ℕ)))
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hcoeff : (f.coeff i).natDegree < p :=
        lt_of_le_of_lt (Finset.le_sup (f := fun j => (f.coeff j).natDegree)
          (s := Finset.range (f.natDegree + 1)) (Finset.mem_range.mpr (by omega))) hM
      have hbound : ((f.coeff i).map φ * X ^ (p * i)).natDegree <
          p * f.natDegree := by
        calc
          _ ≤ (f.coeff i).natDegree + p * i :=
            (natDegree_mul_le).trans (Nat.add_le_add natDegree_map_le (natDegree_X_pow_le _))
          _ < p + p * i := Nat.add_lt_add_right hcoeff _
          _ = p * (i + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
          _ ≤ p * f.natDegree := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hi')
      omega
    rw [natDegree_add_eq_right_of_natDegree_lt hlow, coeff_natDegree,
      natDegree_mul_X_pow _ hne, hlc, Nat.add_comm, Nat.mul_comm]

end Polynomial
