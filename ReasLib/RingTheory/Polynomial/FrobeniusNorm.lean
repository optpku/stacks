/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Polynomial.FrobeniusSpecialization
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Norm.Defs

/-!
# Norms from Frobenius-graph specializations

This file packages the polynomial relation defining an adjoined root and the
corresponding specialized algebra norm over `(ZMod p)[X]`.
-/

@[expose] public section

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

universe u v

namespace Polynomial

/-- The relation polynomial `h(Y) - X` in `R[X][Y]`. -/
def adjoinRootPoly {R : Type u} [CommRing R] (h : R[X]) : R[X][Y] :=
  h.map C - C X

/-- `adjoinRootPoly h` is monic when `h` is monic of positive degree. -/
theorem adjoinRootPoly_monic {R : Type u} [CommRing R] {h : R[X]}
    (hh : h.Monic) (hd : 0 < h.natDegree) :
    (adjoinRootPoly h).Monic := by
  apply (hh.map C).sub_of_left
  apply degree_lt_degree
  simpa only [natDegree_C, natDegree_map_eq_of_injective C_injective] using hd

/-- `adjoinRootPoly h` has the same natural degree as `h` when `h` is monic of
positive degree. -/
theorem adjoinRootPoly_natDegree {R : Type u} [CommRing R] {h : R[X]}
    (hh : h.Monic) (hd : 0 < h.natDegree) :
    (adjoinRootPoly h).natDegree = h.natDegree := by
  simp only [adjoinRootPoly, natDegree_sub_C, natDegree_map_eq_of_injective C_injective]

/-- Reduction of coefficients commutes with forming `adjoinRootPoly`. -/
theorem adjoinRootPoly_map {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (h : R[X]) :
    adjoinRootPoly (h.map φ) = (adjoinRootPoly h).map (mapRingHom φ) := by
  simp [adjoinRootPoly, Polynomial.map_sub, map_map, mapRingHom_comp_C]

/-- `AdjoinRoot (adjoinRootPoly h)` is free as an `R[X]`-module when `h` is monic
of positive degree. -/
theorem moduleFree_adjoinRootPoly {R : Type u} [CommRing R] {h : R[X]}
    (hh : h.Monic) (hd : 0 < h.natDegree) :
    Module.Free R[X] (AdjoinRoot (adjoinRootPoly h)) := by
  exact (adjoinRootPoly_monic hh hd).free_adjoinRoot

/-- `AdjoinRoot (adjoinRootPoly h)` is finite as an `R[X]`-module when `h` is monic
of positive degree. -/
theorem moduleFinite_adjoinRootPoly {R : Type u} [CommRing R] {h : R[X]}
    (hh : h.Monic) (hd : 0 < h.natDegree) :
    Module.Finite R[X] (AdjoinRoot (adjoinRootPoly h)) := by
  exact (adjoinRootPoly_monic hh hd).finite_adjoinRoot

/-- The specialized norm of `g` over the adjoined-root algebra defined by `h` modulo
the prime-indexed coefficient reduction. -/
def algebraNormSpecialize (h : ℤ[X]) (p : ℕ) (g : ℤ[X][Y]) : (ZMod p)[X] :=
  Algebra.norm (Polynomial (ZMod p))
    (aeval (AdjoinRoot.root (adjoinRootPoly (h.map (Int.castRingHom (ZMod p)))))
      (intEvalXPowMod p g))

/-- The specialized norm is the algebra norm of the Frobenius-graph specialization
inside the corresponding adjoined-root algebra. -/
theorem algebraNormSpecialize_spec (h : ℤ[X]) (p : ℕ) (g : ℤ[X][Y]) :
    algebraNormSpecialize h p g =
      Algebra.norm (Polynomial (ZMod p))
        (aeval (AdjoinRoot.root (adjoinRootPoly (h.map (Int.castRingHom (ZMod p)))))
          (intEvalXPowMod p g)) := rfl

/-- The norm of the distinguished root is read from the monic relation. -/
private theorem norm_root_monic {R : Type*} [CommRing R] (q : R[X]) (hm : q.Monic) :
    Algebra.norm R (AdjoinRoot.root q) = (-1) ^ q.natDegree * q.coeff 0 := by
  let b := AdjoinRoot.powerBasis' hm
  have hmin : minpoly R (AdjoinRoot.root q) = q := by
    symm
    refine minpoly.unique' R _ hm (by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]) ?_
    intro s hs
    apply or_iff_not_imp_left.mpr
    intro hne hz
    exact AdjoinRoot.mk_ne_zero_of_degree_lt hm hne hs (by rwa [AdjoinRoot.aeval_eq] at hz)
  have hn := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly b
  simpa [b, hmin] using hn

/-- A quadratic cover produces a term whose degree has slope one half at odd primes. -/
private theorem norm_frobenius_sub (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    algebraNormSpecialize (X ^ 2) p (Y - C X) + X ^ p + X =
      C (2 : ZMod p) * X ^ (p / 2 + 1) := by
  classical
  let q := adjoinRootPoly ((X ^ 2 : ℤ[X]).map (Int.castRingHom (ZMod p)))
  let z := AdjoinRoot.root q
  have hq : q = Y ^ 2 - C X := by simp [q, adjoinRootPoly]
  have hm : q.Monic := by rw [hq]; exact monic_X_pow_sub_C X (by decide)
  let b := AdjoinRoot.powerBasis' hm
  have hd : q.natDegree = 2 := by simp [hq]
  have hz : z ^ 2 = algebraMap (ZMod p)[X] (AdjoinRoot q) X := by
    have hzero : aeval z q = 0 := by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    apply sub_eq_zero.mp
    simpa [hq] using hzero
  have hp := (Fact.out : p.Prime)
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have hpk : p = 2 * (p / 2) + 1 := by omega
  have heq : z ^ p - z = z * algebraMap (ZMod p)[X] (AdjoinRoot q) (X ^ (p / 2) - 1) := by
    calc
      z ^ p - z = z ^ (2 * (p / 2) + 1) - z :=
        congrArg (fun n : ℕ => z ^ n - z) hpk
      _ = _ := by
        rw [pow_add, pow_mul, hz]
        simp only [map_sub, map_pow, map_one, pow_one]
        ring
  have hspec : intEvalXPowMod p (Y - C X) = X ^ p - X := by
    simp [intEvalXPowMod, map_sub, evalXPowRingHom_Y, evalXPowRingHom_C]
  have hnorm : algebraNormSpecialize (X ^ 2) p (Y - C X) =
      -X * (X ^ (p / 2) - 1) ^ 2 := by
    change Algebra.norm (ZMod p)[X]
      (aeval z (intEvalXPowMod p (Y - C X))) = _
    rw [hspec, map_sub, map_pow, aeval_X, heq, map_mul,
      Algebra.norm_algebraMap_of_basis b.basis, Fintype.card_fin]
    change Algebra.norm (ZMod p)[X] (AdjoinRoot.root q) *
      (X ^ (p / 2) - 1) ^ q.natDegree = _
    rw [norm_root_monic q hm, hd]
    simp [hq]
  have hpow : (X : (ZMod p)[X]) ^ p = X ^ (2 * (p / 2) + 1) :=
    congrArg (fun n : ℕ => (X : (ZMod p)[X]) ^ n) hpk
  rw [hnorm, hpow]
  simp only [pow_add, pow_mul, pow_one, map_ofNat]
  ring


/-- There are a monic positive-degree relation and a bivariate polynomial whose
specialized norms cannot all be interpolated by one integer bivariate polynomial. -/
theorem exists_not_eq_algebraNormSpecialize :
    ∃ (h : ℤ[X]), h.Monic ∧ 0 < h.natDegree ∧ ∃ (g : ℤ[X][Y]),
      ¬ ∃ (f : ℤ[X][Y]), ∀ (p : ℕ) [Fact p.Prime],
        intEvalXPowMod p f = algebraNormSpecialize h p g := by
  refine ⟨X ^ 2, monic_X_pow 2, by simp, Y - C X, ?_⟩
  rintro ⟨f, hf⟩
  let F := f + Y + C X
  have hspec (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
      intEvalXPowMod p F = C (2 : ZMod p) * X ^ (p / 2 + 1) := by
    have hmap : intEvalXPowMod p F = intEvalXPowMod p f + X ^ p + X := by
      simp [F, intEvalXPowMod, evalXPowRingHom_Y, evalXPowRingHom_C]
    rw [hmap, hf]
    exact norm_frobenius_sub p hp2
  have hdeg (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
      (intEvalXPowMod p F).natDegree = p / 2 + 1 := by
    have htwo : (2 : ZMod p) ≠ 0 := by
      intro h
      have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).mp h
      have hle := Nat.le_of_dvd (by decide : 0 < 2) hdiv
      have hp := (Fact.out : p.Prime).one_lt
      omega
    rw [hspec p hp2, natDegree_mul_X_pow _ (C_ne_zero.mpr htwo), natDegree_C, zero_add]
  have hF : F ≠ 0 := by
    intro hzero
    letI : Fact (Nat.Prime 3) := ⟨by decide⟩
    have ht := hdeg 3 (by decide)
    simp [hzero, intEvalXPowMod] at ht
  obtain ⟨N, hN⟩ := natDegree_intEvalXPowMod hF
  obtain ⟨p, hlarge, hp⟩ := Nat.exists_infinite_primes (max N (2 * F.leadingCoeff.natDegree + 3))
  letI : Fact p.Prime := ⟨hp⟩
  have hpN : N ≤ p := (le_max_left _ _).trans hlarge
  have hpL : 2 * F.leadingCoeff.natDegree + 3 ≤ p := (le_max_right _ _).trans hlarge
  have hp2 : p ≠ 2 := by omega
  have heq := hN p hp hpN
  rw [hdeg p hp2] at heq
  by_cases hd : F.natDegree = 0
  · simp only [hd, Nat.zero_mul, zero_add] at heq
    omega
  · have hle : p ≤ F.natDegree * p := Nat.le_mul_of_pos_left p (Nat.pos_of_ne_zero hd)
    omega

/-- For every monic positive-degree relation and every nonzero bivariate polynomial,
some nonzero bivariate polynomial has all the specialized norms as divisors. -/
theorem exists_dvd_algebraNormSpecialize (h : ℤ[X]) (hh : h.Monic)
    (hd : 0 < h.natDegree) (g : ℤ[X][Y]) (hg : g ≠ 0) :
    ∃ (f : ℤ[X][Y]), f ≠ 0 ∧ ∀ (p : ℕ) [Fact p.Prime],
      algebraNormSpecialize h p g ∣ intEvalXPowMod p f := sorry

namespace FrobeniusNorm

/-- A nonzero integer bivariate polynomial has split degrees and, at all
sufficiently large primes, a factorization whose first factor has degree
`d1 * p + d1'`, with both slopes positive. -/
def splitFactorization (f : ℤ[X][Y]) (d1 d2 d1' d2' : ℕ) : Prop :=
  f ≠ 0 ∧ f.natDegree = d1 + d2 ∧ f.leadingCoeff.natDegree = d1' + d2' ∧
    0 < d1 ∧ 0 < d2 ∧
      ∃ N : ℕ, ∀ p : ℕ, p.Prime → N ≤ p →
        ∃ f1 f2 : (ZMod p)[X],
          intEvalXPowMod p f = f1 * f2 ∧ f1.natDegree = d1 * p + d1'

/-- A fixed monic positive-degree relation and a fixed integer bivariate
polynomial have specialized norms dividing the Frobenius specializations of `f`
at all sufficiently large primes; unit norm divisors are permitted. -/
def literalNormDivisor (f : ℤ[X][Y]) : Prop :=
  ∃ h : ℤ[X], h.Monic ∧ 0 < h.natDegree ∧ ∃ g : ℤ[X][Y],
    ∃ N : ℕ, ∀ p : ℕ, p.Prime → N ≤ p →
      algebraNormSpecialize h p g ∣ intEvalXPowMod p f

/-- The proposition that every integer bivariate polynomial admitting an
eventual split-degree factorization admits an eventual specialized norm divisor. -/
def splitFactorizationImpliesNormDivisor : Prop :=
  ∀ (f : ℤ[X][Y]) (d1 d2 d1' d2' : ℕ),
    splitFactorization f d1 d2 d1' d2' → literalNormDivisor f

/-- For a monic positive-degree relation `h`, the specialized norm of `1` is
a unit dividing every Frobenius specialization, so every `f` admits a literal
norm divisor. -/
theorem literalNormDivisor_one (f : ℤ[X][Y]) (h : ℤ[X])
    (hh : h.Monic) (hd : 0 < h.natDegree) :
    (∀ p : ℕ, p.Prime →
      IsUnit (algebraNormSpecialize h p 1) ∧
        algebraNormSpecialize h p 1 ∣ intEvalXPowMod p f) ∧
    literalNormDivisor f := by
  have hone (p : ℕ) : algebraNormSpecialize h p 1 = 1 := by
    simp [algebraNormSpecialize, intEvalXPowMod]
  constructor
  · intro p _
    simp [hone]
  · exact ⟨h, hh, hd, 1, 0, fun p _ _ => by simp [hone]⟩

end FrobeniusNorm

end Polynomial
