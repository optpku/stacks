/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.Matrix.Quotient
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Ring.Parity

@[expose] public section

noncomputable section

universe u

open CategoryTheory HomologicalComplex

namespace Matrix

variable {R : Type u} [CommRing R] {n : ℕ}

/-- The period-two differential on the free module over the principal quotient,
using `B` in even degrees and `A` in odd degrees. -/
def periodicDiff (A B : Matrix (Fin n) (Fin n) R) (f : R) (i : ℤ) :
    ModuleCat.of (R ⧸ Ideal.span {f}) (Fin n → R ⧸ Ideal.span {f}) ⟶
      ModuleCat.of (R ⧸ Ideal.span {f}) (Fin n → R ⧸ Ideal.span {f}) :=
  ModuleCat.ofHom (toLinQuotient (if Even i then B else A) f)

/-- Adjacent period-two differentials compose to zero. -/
theorem periodicDiff_comp (A B : Matrix (Fin n) (Fin n) R) {f : R}
    (hAB : A * B = f • 1) (hf : f ∈ nonZeroDivisors R) (i : ℤ) :
    periodicDiff A B f i ≫ periodicDiff A B f (i + 1) = 0 := sorry

/-- The explicit bi-infinite period-two cochain complex associated to a matrix
factorization. -/
def periodicCochain (A B : Matrix (Fin n) (Fin n) R) {f : R}
    (hAB : A * B = f • 1) (hf : f ∈ nonZeroDivisors R) :
    CochainComplex (ModuleCat (R ⧸ Ideal.span {f})) ℤ :=
  CochainComplex.of
    (fun _ ↦ ModuleCat.of (R ⧸ Ideal.span {f}) (Fin n → R ⧸ Ideal.span {f}))
    (periodicDiff A B f) (periodicDiff_comp A B hAB hf)

/-- Every term of the period-two complex is the specified free quotient module. -/
theorem periodicCochain_X (A B : Matrix (Fin n) (Fin n) R) {f : R}
    (hAB : A * B = f • 1) (hf : f ∈ nonZeroDivisors R) (i : ℤ) :
    (periodicCochain A B hAB hf).X i =
      ModuleCat.of (R ⧸ Ideal.span {f}) (Fin n → R ⧸ Ideal.span {f}) := sorry

/-- The differential in each adjacent degree is the period-two differential. -/
theorem periodicCochain_d (A B : Matrix (Fin n) (Fin n) R) {f : R}
    (hAB : A * B = f • 1) (hf : f ∈ nonZeroDivisors R) (i : ℤ) :
    (periodicCochain A B hAB hf).d i (i + 1) = periodicDiff A B f i := sorry

/-- Even-degree differentials are induced by `B`. -/
theorem periodicCochain_d_even (A B : Matrix (Fin n) (Fin n) R) {f : R}
    (hAB : A * B = f • 1) (hf : f ∈ nonZeroDivisors R) {i : ℤ} (hi : Even i) :
    (periodicCochain A B hAB hf).d i (i + 1) = ModuleCat.ofHom (toLinQuotient B f) := sorry

/-- Odd-degree differentials are induced by `A`. -/
theorem periodicCochain_d_odd (A B : Matrix (Fin n) (Fin n) R) {f : R}
    (hAB : A * B = f • 1) (hf : f ∈ nonZeroDivisors R) {i : ℤ} (hi : Odd i) :
    (periodicCochain A B hAB hf).d i (i + 1) = ModuleCat.ofHom (toLinQuotient A f) := sorry

/-- The alternating period-two complex is acyclic for a regular matrix
factorization. -/
theorem periodicCochain_acyclic [NeZero n] (A B : Matrix (Fin n) (Fin n) R) {f : R}
    (hAB : A * B = f • 1) (hf : f ∈ nonZeroDivisors R) :
    (periodicCochain A B hAB hf).Acyclic := sorry

end Matrix
