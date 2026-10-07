module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Topology.KrullDimension.Equidimensional

@[expose] public section

/-!
# Dimension of Intersections in Affine Space

This module records a componentwise Krull-dimension bound for intersections
of equidimensional closed subsets of affine space.
-/

open TopologicalSpace

universe u

namespace MvPolynomial

variable {k : Type u} [Field k]
variable (n r s : ℕ)

/-- If two closed subsets of affine `n`-space are equidimensional of dimensions
`r` and `s`, then every irreducible component of their intersection has dimension
at least `r + s - n`. -/
@[stacks 0B2Q "affine-space intersection dimension bound"]
theorem topologicalKrullDim_irreducibleComponent_quotient_sup_ge_add_sub
    (I J : Ideal (MvPolynomial (Fin n) k))
    [EquidimensionalSpace (PrimeSpectrum (MvPolynomial (Fin n) k ⧸ I))]
    [EquidimensionalSpace (PrimeSpectrum (MvPolynomial (Fin n) k ⧸ J))]
    (hXdim : topologicalKrullDim (PrimeSpectrum (MvPolynomial (Fin n) k ⧸ I)) =
      ((r : ℕ) : WithBot ℕ∞))
    (hYdim : topologicalKrullDim (PrimeSpectrum (MvPolynomial (Fin n) k ⧸ J)) =
      ((s : ℕ) : WithBot ℕ∞)) :
    ∀ Z : irreducibleComponents (PrimeSpectrum (MvPolynomial (Fin n) k ⧸ (I ⊔ J))),
      ((r + s - n : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim Z := sorry

end MvPolynomial
