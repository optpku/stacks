/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# The univariate cusp subalgebra

This file records the subalgebra `k[X ^ 2, X ^ 3]` of the polynomial ring `k[X]`.
-/

@[expose] public section

noncomputable section

universe u

namespace Polynomial

/-- The subalgebra `k[X ^ 2, X ^ 3]` of the polynomial ring `k[X]`. -/
def cuspSubalgebra (k : Type u) [CommRing k] : Subalgebra k (Polynomial k) :=
  Algebra.adjoin k ({X ^ 2, X ^ 3} : Set (Polynomial k))

namespace Cusp

/-- The cusp subalgebra is the `k`-adjoin of `X ^ 2` and `X ^ 3`. -/
theorem eq_adjoin (k : Type u) [CommRing k] :
    cuspSubalgebra k = Algebra.adjoin k ({X ^ 2, X ^ 3} : Set (Polynomial k)) :=
  sorry

/-- The square of the indeterminate lies in the cusp subalgebra. -/
theorem X_pow_two_mem (k : Type u) [CommRing k] :
    X ^ 2 ∈ cuspSubalgebra k :=
  sorry

/-- The cube of the indeterminate lies in the cusp subalgebra. -/
theorem X_pow_three_mem (k : Type u) [CommRing k] :
    X ^ 3 ∈ cuspSubalgebra k :=
  sorry

end Cusp

end Polynomial
