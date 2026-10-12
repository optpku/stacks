/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Localization.FractionRing
public import ReasLib.Algebra.Module.Injective.Hull
public import ReasLib.Algebra.Module.Submodule.Essential
public import ReasLib.RingTheory.Ideal.MinimalPrime.Injective

@[expose] public section

universe u v

namespace IsFractionRing

/-- A fraction field of a domain is injective as a module over the domain. -/
instance injectiveModule
    (R : Type u) [CommRing R] [IsDomain R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K] :
    Module.Injective R K := sorry

/-- The canonical map from a domain to a fraction field is an injective hull. -/
@[stacks 08Y5]
theorem algebraMap_isInjectiveHull
    (R : Type u) [CommRing R] [IsDomain R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K] :
    (Algebra.linearMap R K).IsInjectiveHull := sorry

end IsFractionRing
