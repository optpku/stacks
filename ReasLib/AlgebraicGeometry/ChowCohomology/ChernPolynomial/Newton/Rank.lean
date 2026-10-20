module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernPolynomial.Newton

@[expose] public section

namespace AlgebraicGeometry.ChernPolynomial.Newton

/-- The degree-zero augmented Newton polynomial cannot be expressed as a polynomial in the
positive Chern variables, so these variables do not recover the rank variable. -/
theorem augmented_zero_not_mem_rename_succ :
    augmented 0 ∉ Set.range
      (MvPolynomial.rename Nat.succ : MvPolynomial ℕ ℤ → MvPolynomial ℕ ℤ) := sorry

end AlgebraicGeometry.ChernPolynomial.Newton
