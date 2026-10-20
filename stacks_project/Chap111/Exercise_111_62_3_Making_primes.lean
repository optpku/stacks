/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Data.Complex.Basic
public import ReasLib.RingTheory.MvPolynomial.TwoPointPrimes
import StacksCheckRecall

@[expose] public section

/- Exercise 111.62.3 (Making primes): there are infinitely many distinct prime ideals
`p` of `MvPolynomial (Fin 2) ℂ` such that `PrimeSpectrum.zeroLocus p` contains
`pointToPoint 0` and `pointToPoint 1`, the closed points corresponding to `(x, y)`
and `(x - 1, y - 1)`. -/
@[stacks 0FWM] #check
  (MvPolynomial.infinite_primes_zeroLocus_origin_one :
    {p : Ideal (MvPolynomial (Fin 2) ℂ) |
        p.IsPrime ∧
          MvPolynomial.pointToPoint (0 : Fin 2 → ℂ) ∈
            PrimeSpectrum.zeroLocus (p : Set (MvPolynomial (Fin 2) ℂ)) ∧
          MvPolynomial.pointToPoint (1 : Fin 2 → ℂ) ∈
            PrimeSpectrum.zeroLocus (p : Set (MvPolynomial (Fin 2) ℂ))}.Infinite)
