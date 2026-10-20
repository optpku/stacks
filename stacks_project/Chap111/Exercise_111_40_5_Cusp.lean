module

public import ReasLib.RingTheory.Polynomial.Cusp

/-!
# The univariate cusp subalgebra

This file records the subalgebra `k[X ^ 2, X ^ 3]` of the polynomial ring `k[X]`.
-/

@[expose] public section

universe u
/-! The reusable cusp subalgebra is owned by `ReasLib.RingTheory.Polynomial.Cusp`. -/

#check (@Polynomial.cuspSubalgebra :
  (k : Type u) → [CommRing k] → Subalgebra k (Polynomial k))
