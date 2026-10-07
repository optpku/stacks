module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

noncomputable section

universe u

open CategoryTheory Abelian MvPolynomial

namespace MvPolynomial

/-- Exercise 111.11.4: for a field `k`, writing `R = MvPolynomial ℕ k` and
`I = idealOfVars ℕ k`, the module
`Ext (ModuleCat.of R (R ⧸ I)) (ModuleCat.of R (R ⧸ I)) 1` is not a finite `R`-module.
This cannot happen if `R` is Noetherian, by Algebra Lemma 10.71.9 /
`ModuleCat.finite_ext`. -/
@[stacks 0CRF]
theorem ext_one_quotient_idealOfVars_not_finite (k : Type u) [Field k] :
    ¬ Module.Finite (MvPolynomial ℕ k)
      (Abelian.Ext
        (ModuleCat.of (MvPolynomial ℕ k) (MvPolynomial ℕ k ⧸ idealOfVars ℕ k))
        (ModuleCat.of (MvPolynomial ℕ k) (MvPolynomial ℕ k ⧸ idealOfVars ℕ k)) 1) := sorry

end MvPolynomial
