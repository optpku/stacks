/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.HilbertPolynomial

@[expose] public section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- On projective space of dimension at least two over any field, there exists a coherent
module with Hilbert polynomial `t² / 2 + t / 2 - 1`. -/
theorem exists_isHilbertPolynomial_quadratic
    (k : Type u) [Field k] (n : ℕ) (hn : 2 ≤ n) :
    ∃ (ℱ : (scheme k n).Modules) (hcoherent : ℱ.IsCoherent),
      IsHilbertPolynomial k n ℱ
        (Polynomial.C (1 / 2 : ℚ) * Polynomial.X ^ 2 +
          Polynomial.C (1 / 2 : ℚ) * Polynomial.X - 1) := sorry

end AlgebraicGeometry.ProjectiveSpace
