/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal

@[expose] public section

noncomputable section

universe u

open CategoryTheory Abelian MvPolynomial

namespace MvPolynomial

/-- If `k` is a field, the degree-one self-Ext of the quotient of `MvPolynomial ℕ k`
by the ideal of variables is not a finite module over `MvPolynomial ℕ k`. -/
theorem ext_one_quotient_idealOfVars_not_finite (k : Type u) [Field k] :
    ¬ Module.Finite (MvPolynomial ℕ k)
      (Abelian.Ext
        (ModuleCat.of (MvPolynomial ℕ k) (MvPolynomial ℕ k ⧸ idealOfVars ℕ k))
        (ModuleCat.of (MvPolynomial ℕ k) (MvPolynomial ℕ k ⧸ idealOfVars ℕ k)) 1) := sorry

end MvPolynomial
