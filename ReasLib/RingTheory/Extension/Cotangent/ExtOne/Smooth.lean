/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Extension.Cotangent.ExtOne
public import Mathlib.RingTheory.Smooth.Basic

@[expose] public section

universe u

namespace RingHom.SquareZeroExtension

/-- Every first extension class of the naive cotangent complex of a formally
smooth algebra vanishes, with arbitrary module coefficients. -/
theorem extOneNaiveCotangent_eq_zero_of_formallySmooth
    (A B N : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] [Algebra.FormallySmooth A B]
    (ξ : extOneNaiveCotangent A B N) : ξ = 0 :=
  sorry

end RingHom.SquareZeroExtension
