module

public import Mathlib.RingTheory.Length
public import ReasLib.RingTheory.Ideal.MinimalPrime.TopDimension
public import ReasLib.RingTheory.RegularLocalRing.Parameters
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Minimal-prime bounds from parameter ideals

This leaf relates the top-dimensional minimal-prime locus to the length of a
quotient by a system of parameters.

@stack 0BWX
-/

universe u

open IsLocalRing

namespace IsLocalRing.IsSystemOfParameters

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Lemma 15.126.8: the number of top-dimensional minimal primes is at most the length of the
quotient by any system of parameters. -/
@[stacks 0BWX "Lemma 15.126.8, top-dimensional minimal-prime length bound"]
theorem topDim_encard_le_length
    {d : ℕ} {g : Fin d → maximalIdeal R} (hg : IsSystemOfParameters g) :
    (minimalPrimes.topDim R).encard ≤
      Module.length R (R ⧸ parameterIdeal g) := sorry
-- Proof strategy: separate `d = 0` from positive dimension.  In dimension
-- zero, construct a Hilbert--Samuel polynomial whose multiplicity numerator
-- dominates the minimal-prime count and apply the 0BWW multiplicity bound.  In
-- positive dimension, pass through the reduced diagonal map, transfer the
-- degree-`d` coefficient to the reduced quotient, apply the same multiplicity
-- bound there, and compare the reduced parameter quotient length with the
-- original one.

end IsLocalRing.IsSystemOfParameters
