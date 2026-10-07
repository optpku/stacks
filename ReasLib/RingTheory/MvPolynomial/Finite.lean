module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite homogeneous multivariate-polynomial pieces

This leaf records the canonical finiteness facts for the degree pieces of a multivariate
polynomial ring.  The finite-variable hypothesis belongs on the index type, rather than being
reconstructed at each Hilbert-function consumer.
-/

@[expose] public section

namespace MvPolynomial

universe u v

variable {σ : Type u} {R : Type v} [CommSemiring R] [Finite σ]

namespace homogeneousSubmodule

/-- A homogeneous degree piece is finitely generated whenever the variable type is finite. -/
@[stacks 00K2 "finite homogeneous polynomial component"]
noncomputable instance moduleFinite (n : ℕ) :
    Module.Finite R (MvPolynomial.homogeneousSubmodule σ R n) := sorry

variable {k : Type v} [Field k] [Fintype σ]

/-- The dimension of a finite-variable homogeneous piece is the multichoose number of monomials.
-/
@[stacks 00K2 "homogeneous polynomial component dimension"]
theorem finrank (n : ℕ) :
    Module.finrank k (MvPolynomial.homogeneousSubmodule σ k n) =
      (Fintype.card σ).multichoose n := sorry

/-- The finite-variable specialization of `finrank`, with the cardinality reduced to the number of
variables. -/
@[stacks 00K2 "Fin-indexed homogeneous polynomial component dimension"]
theorem finrank_fin (d n : ℕ) :
    Module.finrank k (MvPolynomial.homogeneousSubmodule (Fin d) k n) = d.multichoose n := sorry

end homogeneousSubmodule

end MvPolynomial
