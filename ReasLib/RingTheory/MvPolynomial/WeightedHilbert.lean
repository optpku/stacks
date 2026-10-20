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
theorem weight_apply (i : Fin 2) : weight i = if i = 0 then 2 else 3 := sorry

/-- The first variable has weight `2`. -/
theorem weight_zero : weight 0 = 2 := sorry

/-- The second variable has weight `3`. -/
theorem weight_one : weight 1 = 3 := sorry

variable (k : Type u) [Field k]

/-- The polynomial ring `k[x, y]`, with variables indexed by `Fin 2`. -/
abbrev PolynomialRing :=
  MvPolynomial (Fin 2) k

/-- The weighted homogeneous grading on `k[x, y]` of type `(2, 3)`. -/
abbrev grading : ℕ → Submodule k (PolynomialRing k) :=
  weightedHomogeneousSubmodule k weight

/-- Membership in `grading k n` is weighted homogeneity of degree `n`. -/
theorem mem_grading_iff (n : ℕ) (f : PolynomialRing k) :
    f ∈ grading k n ↔ IsWeightedHomogeneous weight f n := sorry

/-- The canonical graded-algebra structure on the type-`(2, 3)` weighted polynomial grading. -/
noncomputable instance instGradedAlgebra : GradedAlgebra (grading k) :=
  weightedGradedAlgebra k weight

/-- The integer-indexed grading of `k[x, y]` obtained by extending the natural grading by `⊥`. -/
abbrev integerGrading : ℤ → Submodule k (PolynomialRing k) :=
  DirectSum.Decomposition.natToIntGrading (grading k)

/-- On nonnegative degrees, the integer grading agrees with the natural weighted grading. -/
theorem integerGrading_of_nonneg {n : ℤ} (hn : 0 ≤ n) :
    integerGrading k n = grading k n.toNat := sorry

/-- On negative degrees, the integer grading is the zero submodule. -/
theorem integerGrading_of_neg {n : ℤ} (hn : n < 0) :
    integerGrading k n = ⊥ := sorry

/-- Each degree piece of the type-`(2, 3)` integer grading is a finite `k`-module. -/
instance instLocallyFinite : GradedModule.LocallyFinite (integerGrading k) :=
  sorry

/-- The Hilbert function of the type-`(2, 3)` weighted polynomial ring is the `k`-dimension
of the degree piece. -/
theorem hilbertFunction_eq_finrank (k : Type u) [Field k] (n : ℤ) :
    hilbertFunction (K0.Finite.genericRank.{u, u} k) (integerGrading k) n =
      Module.finrank k (integerGrading k n) :=
  sorry

/-- In nonnegative degrees, the Hilbert function counts monomials `x^a y^b` of weighted
degree `n`. -/
theorem hilbertFunction_eq_card (k : Type u) [Field k] {n : ℤ} (hn : 0 ≤ n) :
    hilbertFunction (K0.Finite.genericRank.{u, u} k) (integerGrading k) n =
      Nat.card {p : ℕ × ℕ | 2 * p.1 + 3 * p.2 = n.toNat} :=
  sorry

/-- The Hilbert function of `k[x, y]` with weights `2` and `3` is zero in negative degrees
and equals `n / 6 + if n % 6 = 1 then 0 else 1` in nonnegative degrees. -/
theorem hilbertFunction_eq (k : Type u) [Field k] (n : ℤ) :
    hilbertFunction (K0.Finite.genericRank.{u, u} k) (integerGrading k) n =
      if n < 0 then 0 else n / 6 + if n % 6 = 1 then 0 else 1 :=
  sorry

/-- The polynomial ring `k[x, y]` with weights `2` and `3` has no Hilbert polynomial
with respect to dimension over `k`. -/
theorem not_hasHilbertPolynomial (k : Type u) [Field k] :
    ¬ HasHilbertPolynomial (K0.Finite.genericRank.{u, u} k) (integerGrading k) :=
  sorry

end MvPolynomial.Weights23
