/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.Maximal.MvPolynomial
import StacksCheckRecall

@[expose] public section

/- Exercise 111.53.5 (1): Chevalley's theorem implies that a maximal ideal of
`ℤ[x₁, …, xₙ]` contracts to a maximal ideal of `ℤ`. -/
@[stacks 069V] #check
  (MvPolynomial.isMaximal_under_int_of_isMaximal :
    ∀ {n : ℕ} (p : Ideal (MvPolynomial (Fin n) ℤ)), [p.IsMaximal] →
      (p.under ℤ).IsMaximal)

/- Exercise 111.53.5 (2): the Hilbert Nullstellensatz implies that the residue field
`p.ResidueField` of a maximal ideal `p ⊂ ℤ[x₁, …, xₙ]` is finite. -/
@[stacks 069V] #check
  (MvPolynomial.finite_residueField_of_isMaximal_int :
    ∀ {n : ℕ} (p : Ideal (MvPolynomial (Fin n) ℤ)), [p.IsMaximal] →
      Finite p.ResidueField)
