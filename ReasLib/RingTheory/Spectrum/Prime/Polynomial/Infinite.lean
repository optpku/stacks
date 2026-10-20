/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Data.Finite.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Defs

@[expose] public section

universe u

open Polynomial

namespace PrimeSpectrum

/-- The prime spectrum of a univariate polynomial ring over any field is infinite. -/
instance instInfinite_polynomial {k : Type u} [Field k] : Infinite (PrimeSpectrum k[X]) := sorry

end PrimeSpectrum
