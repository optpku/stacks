/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Kaehler.Polynomial

@[expose] public section

universe u

namespace KaehlerDifferential

/-- Under the canonical identification of the Kähler differentials of `Polynomial k` with
`Polynomial k`, the differential of `X ^ n` is `C (n : k) * X ^ (n - 1)`. -/
theorem polynomialEquiv_D_X_pow (k : Type u) [Field k] (n : ℕ) :
    polynomialEquiv k (D k (Polynomial k) (Polynomial.X ^ n)) =
      Polynomial.C (n : k) * Polynomial.X ^ (n - 1) := sorry

end KaehlerDifferential
