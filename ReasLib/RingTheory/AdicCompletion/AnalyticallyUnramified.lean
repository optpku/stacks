module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.LocalRing.Quotient

@[expose] public section

/-!
# Analytically Unramified Local Rings

This module defines analytically unramified local rings through reducedness of
their maximal-ideal adic completions.
-/

universe u

open IsLocalRing

namespace PrimeSpectrum

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- A prime quotient of a local ring is local, via the canonical proper-ideal quotient API. -/
@[stacks 05WQ "prime local quotient"]
instance quotient_isLocalRing (p : PrimeSpectrum R) : IsLocalRing (R ⧸ p.asIdeal) :=
  IsLocalRing.quotient p.asIdeal p.isPrime.ne_top

end PrimeSpectrum

section

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- A local ring is analytically unramified when its completion at the maximal ideal
is reduced. -/
@[stacks 032X, mk_iff isAnalyticallyUnramified_iff]
class IsAnalyticallyUnramified : Prop where
  /-- The maximal-ideal adic completion is reduced. -/
  completion_isReduced : IsReduced (AdicCompletion (maximalIdeal R) R)

attribute [instance] IsAnalyticallyUnramified.completion_isReduced

end

section

variable (K : Type u) [Field K]

/-- Fields are analytically unramified. -/
instance IsAnalyticallyUnramified.instOfField : IsAnalyticallyUnramified K := sorry

end

namespace PrimeSpectrum

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- A prime ideal is analytically unramified when its quotient local ring is
analytically unramified. -/
def IsAnalyticallyUnramified (p : PrimeSpectrum R) : Prop :=
  _root_.IsAnalyticallyUnramified (R ⧸ p.asIdeal)

end PrimeSpectrum
