/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AdicCompletion.Congruence
public import ReasLib.RingTheory.MvPolynomial.Solution
public import ReasLib.RingTheory.Regular.GRing
import ReasLib.RingTheory.Smooth.Henselian

@[expose] public section

/-!
# Local Artin approximation

This leaf specializes Artin approximation to the maximal-ideal completion of
a henselian local ring.  Regularity of that one completion map is the core
hypothesis; the G-ring theorem is a separate bridge.
-/

open IsLocalRing MvPolynomial

universe u w x

namespace HenselianLocalRing.ArtinApproximation

/-- Theorem 16.13.1: over a Noetherian henselian local ring with regular
completion map, a formal solution can be approximated by an exact solution
modulo every power of the maximal ideal. -/
@[stacks 07QY]
theorem nonempty
    {R : Type u} [CommRing R] [HenselianLocalRing R] [IsNoetherianRing R]
    [hreg : (algebraMap R
      (AdicCompletion (maximalIdeal R) R)).Regular]
    {sigma : Type w} {iota : Type x} [Finite sigma] [Finite iota]
    (f : iota → MvPolynomial sigma R)
    (aHat : sigma → AdicCompletion (maximalIdeal R) R)
    (hroots : IsSolution f aHat) (N : ℕ) :
    Nonempty (SolutionApproximation f aHat
      (Algebra.ofId R (AdicCompletion (maximalIdeal R) R))
      (AdicCompletion.extendedIdealPow (maximalIdeal R) N)) := sorry

/-- Theorem 16.13.1, G-ring branch: the G-ring hypothesis supplies the
regular completion map for local Artin approximation. -/
@[stacks 07QY "G-ring local branch"]
theorem nonempty_of_isGRing
    {R : Type u} [CommRing R] [HenselianLocalRing R] [IsGRing R]
    {sigma : Type w} {iota : Type x} [Finite sigma] [Finite iota]
    (f : iota → MvPolynomial sigma R)
    (aHat : sigma → AdicCompletion (maximalIdeal R) R)
    (hroots : IsSolution f aHat) (N : ℕ) :
    Nonempty (SolutionApproximation f aHat
      (Algebra.ofId R (AdicCompletion (maximalIdeal R) R))
      (AdicCompletion.extendedIdealPow (maximalIdeal R) N)) := sorry

end HenselianLocalRing.ArtinApproximation
