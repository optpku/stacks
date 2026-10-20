/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AffineSpace.XyPlanes
import StacksCheckRecall

@[expose] public section

open MvPolynomial.XyPlanes

/- Exercise 111.62.4 (No prime): in `ℂ[x, y, z] ⧸ (x * y)`, no prime ideal
has a zero locus containing both points `(0, 1, 5)` and `(1, 0, 7)`. -/
@[stacks 0FWN] #check (MvPolynomial.XyPlanes.not_exists_prime_le_pointIdeals :
  ¬ ∃ p : Ideal CoordinateRing, p.IsPrime ∧ p ≤ pointIdeal015 ∧ p ≤ pointIdeal107)
