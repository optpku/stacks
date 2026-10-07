module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Approximation.Artin.Etale.AtPrime
public import ReasLib.RingTheory.Regular.GRing

@[expose] public section

/-!
# Existence of primewise Artin approximations
-/

open MvPolynomial

universe u w x

namespace PrimeSpectrum.ArtinApproximation.AtPrime

/-- A formal solution in the completed local ring at a prime
admits a bundled exact approximation in an etale neighborhood of that prime. -/
@[stacks 0CAR]
theorem nonempty
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p : PrimeSpectrum R)
    [hreg : (algebraMap (Localization.AtPrime p.asIdeal)
      (CompletedLocalRing p)).Regular]
    {sigma : Type w} {iota : Type x} [Finite sigma] [Finite iota]
    (f : iota → MvPolynomial sigma R) (aHat : sigma → CompletedLocalRing p)
    (hroots : IsSolution f aHat) (N : ℕ) :
    Nonempty (AtPrime.{u, u, w, x} p f aHat N) := sorry

/-- A formal solution over a G-ring admits a primewise etale approximation. -/
@[stacks 0CAR "G-ring prime branch"]
theorem nonempty_of_isGRing
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p : PrimeSpectrum R)
    [IsGRing (Localization.AtPrime p.asIdeal)]
    {sigma : Type w} {iota : Type x} [Finite sigma] [Finite iota]
    (f : iota → MvPolynomial sigma R) (aHat : sigma → CompletedLocalRing p)
    (hroots : IsSolution f aHat) (N : ℕ) :
    Nonempty (AtPrime.{u, u, w, x} p f aHat N) := sorry

end PrimeSpectrum.ArtinApproximation.AtPrime
