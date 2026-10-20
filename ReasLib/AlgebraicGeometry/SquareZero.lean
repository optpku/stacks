module

public import ReasLib.RingTheory.MvPolynomial.SquareZero.Noetherian
public import Mathlib.AlgebraicGeometry.Noetherian

@[expose] public section

universe u v

open AlgebraicGeometry

namespace MvPolynomial.SquareZero

variable {σ : Type u} {k : Type v} [Field k]

/-- The affine scheme of the polynomial quotient by the coordinate squares in infinitely
many variables over a field is not a Noetherian scheme. -/
theorem not_isNoetherian_spec [Infinite σ] :
    ¬ IsNoetherian (Spec (CommRingCat.of (Quotient (σ := σ) (k := k)))) := sorry

end MvPolynomial.SquareZero
