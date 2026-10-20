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
    (adjoinRootPoly h).Monic := sorry

/-- `adjoinRootPoly h` has the same natural degree as `h` when `h` is monic of
positive degree. -/
theorem adjoinRootPoly_natDegree {R : Type u} [CommRing R] {h : R[X]}
    (hh : h.Monic) (hd : 0 < h.natDegree) :
    (adjoinRootPoly h).natDegree = h.natDegree := sorry

/-- Reduction of coefficients commutes with forming `adjoinRootPoly`. -/
theorem adjoinRootPoly_map {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (h : R[X]) :
    adjoinRootPoly (h.map φ) = (adjoinRootPoly h).map (mapRingHom φ) := sorry

/-- `AdjoinRoot (adjoinRootPoly h)` is free as an `R[X]`-module when `h` is monic
of positive degree. -/
theorem moduleFree_adjoinRootPoly {R : Type u} [CommRing R] {h : R[X]}
    (hh : h.Monic) (hd : 0 < h.natDegree) :
    Module.Free R[X] (AdjoinRoot (adjoinRootPoly h)) := sorry

/-- `AdjoinRoot (adjoinRootPoly h)` is finite as an `R[X]`-module when `h` is monic
of positive degree. -/
theorem moduleFinite_adjoinRootPoly {R : Type u} [CommRing R] {h : R[X]}
    (hh : h.Monic) (hd : 0 < h.natDegree) :
    Module.Finite R[X] (AdjoinRoot (adjoinRootPoly h)) := sorry

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
          (intEvalXPowMod p g)) := sorry

/-- There are a monic positive-degree relation and a bivariate polynomial whose
specialized norms cannot all be interpolated by one integer bivariate polynomial. -/
theorem exists_not_eq_algebraNormSpecialize :
    ∃ (h : ℤ[X]), h.Monic ∧ 0 < h.natDegree ∧ ∃ (g : ℤ[X][Y]),
      ¬ ∃ (f : ℤ[X][Y]), ∀ (p : ℕ) [Fact p.Prime],
        intEvalXPowMod p f = algebraNormSpecialize h p g := sorry

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
    literalNormDivisor f := sorry

end FrobeniusNorm

end Polynomial
