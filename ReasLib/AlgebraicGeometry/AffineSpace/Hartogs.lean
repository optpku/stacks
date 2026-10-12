/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AffineSpace.RegularFunctions

@[expose] public section

noncomputable section

universe u

namespace MvPolynomial

/-- Over an algebraically closed field, a regular function on affine space minus a finite
set is polynomial when the affine dimension is at least two. -/
theorem isPolynomial_of_isRegular_compl_finite {k : Type u} [Field k] [IsAlgClosed k]
    {n : ℕ} (hn : 2 ≤ n) {E : Set (Fin n → k)} (hE : E.Finite)
    (φ : (Eᶜ : Set (Fin n → k)) → k) (hφ : IsRegular φ) : IsPolynomial φ := sorry

end MvPolynomial
