module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AdicCompletion.AnalyticallyUnramified
public import ReasLib.RingTheory.Normal.Nagata

@[expose] public section

/-!
# Analytically Unramified Nagata Domains

@stack 0331

This module records the canonical analytic-unramifiedness consequence of the
Nagata condition for local domains.
-/

universe u

namespace NagataRing

variable (R : Type u)

/-- Every local Nagata domain is analytically unramified. -/
@[stacks 0331]
instance analyticallyUnramified
    [CommRing R] [IsLocalRing R] [IsDomain R] [NagataRing R] :
    IsAnalyticallyUnramified R := sorry

end NagataRing
