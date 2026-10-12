/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Approximation.Artin.Etale.AtClosedPoint
public import ReasLib.RingTheory.Regular.GRing

@[expose] public section

/-!
# Existence of closed-point Artin approximations
-/

open IsLocalRing MvPolynomial

universe u w x

namespace PrimeSpectrum.ArtinApproximation.AtClosedPoint

/-- Theorem 16.13.2: a formal solution over a Noetherian local ring with
regular completion map admits a bundled approximation in an etale
neighborhood of the closed point. -/
@[stacks 07QZ]
theorem nonempty
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [hreg : (algebraMap R
      (AdicCompletion (maximalIdeal R) R)).Regular]
    {sigma : Type w} {iota : Type x} [Finite sigma] [Finite iota]
    (f : iota → MvPolynomial sigma R)
    (aHat : sigma → AdicCompletion (maximalIdeal R) R)
    (hroots : IsSolution f aHat) (N : ℕ) :
    Nonempty (AtClosedPoint.{u, u, w, x} f aHat N) := sorry

/-- Theorem 16.13.2, G-ring branch: closed-point etale approximation. -/
@[stacks 07QZ "G-ring closed-point branch"]
theorem nonempty_of_isGRing
    {R : Type u} [CommRing R] [IsLocalRing R] [IsGRing R]
    {sigma : Type w} {iota : Type x} [Finite sigma] [Finite iota]
    (f : iota → MvPolynomial sigma R)
    (aHat : sigma → AdicCompletion (maximalIdeal R) R)
    (hroots : IsSolution f aHat) (N : ℕ) :
    Nonempty (AtClosedPoint.{u, u, w, x} f aHat N) := sorry

end PrimeSpectrum.ArtinApproximation.AtClosedPoint
