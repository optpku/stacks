/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Localization.FractionRing.IntegralClosure

/-!
# Prime localizations of finite integral closures

This leaf records the discrete-valuation consequence at a nonzero prime of an
integral closure in a finite fraction-field extension.  The source-specific
choice of a prime over a closed point belongs to downstream applications.
-/

@[expose] public section

universe u v

namespace FractionRing.IntegralClosure.AtPrime

/-- Tag `00PH`: localizing the integral closure of a one-dimensional Noetherian
domain in a finite fraction-field extension at a nonzero prime gives a discrete
valuation ring.  The dimension-at-most-one typeclass is the reusable core
input; source-facing Krull-dimension equalities are handled by bridges. -/
@[stacks 00PH "DVR at a nonzero prime of a finite integral closure"]
theorem isDiscreteValuationRing_of_ne_bot
    {A : Type u} {L : Type v} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Field L] [Algebra A L] [Algebra (FractionRing A) L]
    [IsScalarTower A (FractionRing A) L]
    [FiniteDimensional (FractionRing A) L] [Ring.DimensionLEOne A]
    (q : PrimeSpectrum (integralClosure A L)) (hq : q.asIdeal ≠ ⊥) :
    IsDiscreteValuationRing (Localization.AtPrime q.asIdeal) := sorry

end FractionRing.IntegralClosure.AtPrime
