/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.MvPolynomial.NontrivialSolution
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

universe u

@[expose] public section

namespace Field

/-- The `C_r` property of a field: every homogeneous multivariate polynomial of
positive degree `d` in `n > d ^ r` variables has a nontrivial solution. -/
def IsCr (K : Type u) [Field K] (r : ℕ) : Prop :=
  ∀ (d n : ℕ), (0 < d ∧ d ^ r < n) →
    ∀ (f : MvPolynomial (Fin n) K), f.IsHomogeneous d →
      ∃ α : Fin n → K, MvPolynomial.IsNontrivialSolution f α

/-- The quantified characterization of the `C_r` property of a field using
homogeneous polynomials of positive degree. -/
theorem isCr_iff (K : Type u) [Field K] (r : ℕ) :
    IsCr K r ↔
      ∀ (d n : ℕ), (0 < d ∧ d ^ r < n) →
        ∀ (f : MvPolynomial (Fin n) K), f.IsHomogeneous d →
          ∃ α : Fin n → K, MvPolynomial.IsNontrivialSolution f α := sorry

end Field
