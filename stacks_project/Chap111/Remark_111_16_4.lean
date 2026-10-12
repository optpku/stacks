/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Jacobson

@[expose] public section

universe u

open MvPolynomial

/-- Remark 111.16.4: this is the Hilbert Nullstellensatz. Closed subsets of
`PrimeSpectrum (MvPolynomial (Fin n) k)` (which correspond to radical ideals by
`PrimeSpectrum.isClosed_iff_zeroLocus_radical_ideal`) are determined by the closed
points they contain: every closed set equals the closure of its intersection with
`closedPoints`. -/
@[stacks 02DQ]
theorem PrimeSpectrum.closure_inter_closedPoints_mvPolynomial
    {k : Type u} [Field k] {n : ℕ}
    {Z : Set (PrimeSpectrum (MvPolynomial (Fin n) k))} (hZ : IsClosed Z) :
    closure (Z ∩ closedPoints (PrimeSpectrum (MvPolynomial (Fin n) k))) = Z := sorry

/-- Closed subsets of `PrimeSpectrum (MvPolynomial (Fin n) k)` that contain the same
closed points coincide. -/
theorem PrimeSpectrum.eq_of_isClosed_inter_closedPoints_eq_mvPolynomial
    {k : Type u} [Field k] {n : ℕ}
    {Z₁ Z₂ : Set (PrimeSpectrum (MvPolynomial (Fin n) k))}
    (hZ₁ : IsClosed Z₁) (hZ₂ : IsClosed Z₂)
    (h : Z₁ ∩ closedPoints (PrimeSpectrum (MvPolynomial (Fin n) k)) =
      Z₂ ∩ closedPoints (PrimeSpectrum (MvPolynomial (Fin n) k))) :
    Z₁ = Z₂ := sorry
