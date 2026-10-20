module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AdicCompletion.AtPrime
public import ReasLib.RingTheory.AdicCompletion.Congruence

@[expose] public section

/-!
# Congruence ideals in completed local rings

This leaf names the extended powers of the maximal ideal in a completed
local ring at a bundled prime.
-/

open IsLocalRing

universe u

namespace PrimeSpectrum

/-- The extension of the `n`th power of the maximal ideal of `R_p` to its
completion. -/
@[stacks 0CAR "completed local maximal-ideal power"]
noncomputable abbrev completedMaximalIdealPow
    {R : Type u} [CommRing R] (p : PrimeSpectrum R) (n : ℕ) :
    Ideal (CompletedLocalRing p) :=
  AdicCompletion.extendedIdealPow
    (maximalIdeal (Localization.AtPrime p.asIdeal)) n

end PrimeSpectrum
