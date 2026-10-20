/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Group.Irreducible.Defs
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.ZMod.Basic

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
    evalXPowRingHom φ n (C q) = q.map φ := sorry

/-- `evalXPowRingHom φ n` sends the inner variable `X` to `X`. -/
theorem evalXPowRingHom_X {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (n : ℕ) :
    evalXPowRingHom φ n (C X) = X := sorry

/-- `evalXPowRingHom φ n` sends the outer variable `Y` to `X ^ n`. -/
theorem evalXPowRingHom_Y {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (n : ℕ) :
    evalXPowRingHom φ n Y = X ^ n := sorry

/-- The specialization `f_p(x) = f(x, x ^ p) mod p` in `(ZMod p)[X]`. -/
def intEvalXPowMod (p : ℕ) (f : ℤ[X][Y]) : (ZMod p)[X] :=
  evalXPowRingHom (Int.castRingHom (ZMod p)) p f

/-- The specialization `intEvalXPowMod p f` is evaluation along the Frobenius graph
followed by reduction of integer coefficients modulo `p`. -/
theorem intEvalXPowMod_spec (p : ℕ) (f : ℤ[X][Y]) :
    intEvalXPowMod p f = evalXPowRingHom (Int.castRingHom (ZMod p)) p f := sorry

/-- The integer bivariate polynomial `Y - C (X + 1)`. -/
def ySubXSucc : ℤ[X][Y] := Y - C (X + 1)

/-- The integer bivariate polynomial `Y ^ 2 - C (X ^ 2) + 1`. -/
def ySqSubXSqAddOne : ℤ[X][Y] := Y ^ 2 - C (X ^ 2) + 1

/-- Frobenius specialization of `Y - C (X + 1)` gives `X ^ p - X - 1`. -/
theorem intEvalXPowMod_ySubXSucc (p : ℕ) :
    intEvalXPowMod p ySubXSucc = X ^ p - X - 1 := sorry

/-- Frobenius specialization of `Y ^ 2 - C (X ^ 2) + 1` gives
`X ^ (2 * p) - X ^ 2 + 1`. -/
theorem intEvalXPowMod_ySqSubXSqAddOne (p : ℕ) :
    intEvalXPowMod p ySqSubXSqAddOne = X ^ (2 * p) - X ^ 2 + 1 := sorry

/-- Some integer bivariate polynomial has irreducible Frobenius specializations
over `ZMod p` for infinitely many primes `p`. -/
theorem exists_intEvalXPowMod_irreducible_infinite :
    ∃ f : ℤ[X][Y], {p : ℕ | p.Prime ∧ Irreducible (intEvalXPowMod p f)}.Infinite := sorry

/-- The polynomial `Y - C (X + 1)` has irreducible Frobenius specializations
over `ZMod p` for infinitely many primes `p`. -/
theorem ySubXSucc_intEvalXPowMod_irreducible_infinite :
    {p : ℕ | p.Prime ∧ Irreducible (intEvalXPowMod p ySubXSucc)}.Infinite := sorry

/-- The polynomial `Y ^ 2 - C (X ^ 2) + 1` has irreducible Frobenius
specializations over `ZMod p` for infinitely many primes `p`. -/
theorem ySqSubXSqAddOne_intEvalXPowMod_irreducible_infinite :
    {p : ℕ | p.Prime ∧ Irreducible (intEvalXPowMod p ySqSubXSqAddOne)}.Infinite := sorry

/-- For every nonzero integer bivariate polynomial, the degree of its Frobenius
specialization is eventually `f.natDegree * p + f.leadingCoeff.natDegree` at primes. -/
theorem natDegree_intEvalXPowMod {f : ℤ[X][Y]} (hf : f ≠ 0) :
    ∃ N : ℕ, ∀ p : ℕ, p.Prime → N ≤ p →
      (intEvalXPowMod p f).natDegree = f.natDegree * p + f.leadingCoeff.natDegree := sorry

end Polynomial
