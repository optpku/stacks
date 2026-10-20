/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Absolutely integrally closed rings

This file owns the intrinsic ring property and its basic polynomial API. Stability
under ring constructions is kept in separate leaves.

@stack 0DCL
-/

open Polynomial

universe u

/-- A commutative ring is absolutely integrally closed if every monic polynomial
splits over the ring. -/
@[stacks 0DCL "absolutely integrally closed rings"]
class IsAbsolutelyIntegrallyClosed (A : Type u) [CommRing A] : Prop where
  /-- Every monic polynomial over an absolutely integrally closed ring splits. -/
  splits (f : A[X]) (hf : f.Monic) : f.Splits

namespace IsAbsolutelyIntegrallyClosed

variable {A : Type u} [CommRing A]

/-- Algebraically closed fields are absolutely integrally closed as rings. -/
@[stacks 0DCL "algebraically closed fields are absolutely integrally closed"]
instance of_isAlgClosed {K : Type u} [Field K] [IsAlgClosed K] :
    IsAbsolutelyIntegrallyClosed K := sorry
-- Proof strategy: use the field splitting theorem from
-- `Mathlib.FieldTheory.IsAlgClosed.Basic` to fill the polynomial `Splits` field.

/-- Every nonconstant monic polynomial over an absolutely integrally closed ring
has a root. -/
theorem exists_root [IsAbsolutelyIntegrallyClosed A] (f : A[X]) (hf : f.Monic)
    (hdeg : f.degree ≠ 0) : ∃ a : A, f.IsRoot a := sorry
-- Proof strategy: apply the `splits` field to `f`, then use
-- `Polynomial.Splits.exists_eval_eq_zero` with `hdeg` to extract a root.

/-- A field that is absolutely integrally closed as a ring is algebraically closed. -/
theorem isAlgClosed {K : Type u} [Field K] [IsAbsolutelyIntegrallyClosed K] :
    IsAlgClosed K := sorry
-- Proof strategy: apply `IsAlgClosed.of_exists_root`; for an irreducible monic polynomial,
-- `Polynomial.degree_pos_of_irreducible` supplies the nonzero-degree hypothesis needed by
-- `exists_root`.

/-- Root existence for nonconstant monic polynomials implies absolute integral
closedness. -/
theorem of_exists_root
    (hroot : ∀ (f : A[X]), f.Monic → f.degree ≠ 0 → ∃ a : A, f.IsRoot a) :
    IsAbsolutelyIntegrallyClosed A := sorry
-- Proof strategy: construct the `splits` field by monic-polynomial degree induction using
-- `hroot`; handle degree zero with `Polynomial.splits_of_natDegree_eq_zero` and factor out
-- `X - C a` in the positive-degree step via `Polynomial.mul_divByMonic_eq_iff_isRoot`.

/-- A ring is absolutely integrally closed exactly when every nonconstant monic
polynomial has a root. -/
@[stacks 0DCM "root criterion for absolute integral closedness"]
theorem iff_forall_monic_exists_root :
    IsAbsolutelyIntegrallyClosed A ↔
      ∀ (f : A[X]), f.Monic → f.degree ≠ 0 → ∃ a : A, f.IsRoot a := sorry
-- Proof strategy: combine `exists_root` with `of_exists_root`; this is the source-facing
-- equivalence and avoids unfolding the class downstream.

end IsAbsolutelyIntegrallyClosed
