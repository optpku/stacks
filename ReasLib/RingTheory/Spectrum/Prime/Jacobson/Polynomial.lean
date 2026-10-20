/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Jacobson

@[expose] public section

universe u v

namespace PrimeSpectrum

/-- Every closed subset of the spectrum of a polynomial ring in finitely many variables over
a Jacobson commutative ring is the closure of the closed points it contains. -/
theorem closure_inter_closedPoints_mvPolynomial
    {R : Type u} [CommRing R] [IsJacobsonRing R] {ι : Type v} [Finite ι]
    {Z : Set (PrimeSpectrum (MvPolynomial ι R))} (hZ : IsClosed Z) :
    closure (Z ∩ closedPoints (PrimeSpectrum (MvPolynomial ι R))) = Z :=
  closure_inter_closedPoints hZ

end PrimeSpectrum
