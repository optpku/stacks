/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs

@[expose] public section

/-!
# Semilocal Rings and the Jacobson Property

@stack 00G5

Obstructions to the Jacobson property for domains with finitely many maximal ideals and for local
rings with nonmaximal prime ideals.
-/

universe u

/-- Example 10.35.8: a domain with finitely many maximal ideals is not Jacobson unless it is a
field. -/
@[stacks 00G5 "finite maximal spectrum consequence"]
theorem not_isJacobsonRing_of_finite_maximalSpectrum_of_not_isField
    {R : Type u} [CommRing R] [IsDomain R] [Finite (MaximalSpectrum R)]
    (hR : ¬ IsField R) : ¬ IsJacobsonRing R := sorry

namespace IsLocalRing

/-- Example 10.35.8: a local ring with a prime ideal distinct from its maximal ideal is not
Jacobson. -/
@[stacks 00G5 "local-ring consequence"]
theorem not_isJacobsonRing_of_exists_prime_ne_maximalIdeal
    {R : Type u} [CommRing R] [IsLocalRing R]
    (hP : ∃ P : Ideal R, P.IsPrime ∧ P ≠ maximalIdeal R) : ¬ IsJacobsonRing R := sorry

end IsLocalRing

namespace IsDiscreteValuationRing

/-- Example 10.35.8: a discrete valuation ring is not a Jacobson ring. -/
@[stacks 00G5 "discrete-valuation-ring consequence"]
theorem not_isJacobsonRing
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    ¬ IsJacobsonRing R := sorry

end IsDiscreteValuationRing
