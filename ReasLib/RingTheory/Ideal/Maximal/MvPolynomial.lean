/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.Finite.Defs
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Jacobson.Ring

@[expose] public section

namespace MvPolynomial

/-- A maximal ideal of a finite-variable polynomial ring over the integers contracts to a maximal ideal of the integers. -/
@[instance]
theorem isMaximal_under_int_of_isMaximal {n : ℕ} (p : Ideal (MvPolynomial (Fin n) ℤ)) [p.IsMaximal] :
    (p.under ℤ).IsMaximal := sorry

/-- The residue field of a maximal ideal of a finite-variable polynomial ring over the integers is finite. -/
@[instance]
theorem finite_residueField_of_isMaximal_int {n : ℕ} (p : Ideal (MvPolynomial (Fin n) ℤ)) [p.IsMaximal] :
    Finite p.ResidueField := sorry

end MvPolynomial
