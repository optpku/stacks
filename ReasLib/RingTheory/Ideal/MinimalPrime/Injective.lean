/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Injective
public import ReasLib.RingTheory.Ideal.MinimalPrime.Localization

@[expose] public section

universe u

namespace minimalPrimes

/-- The localization of a reduced commutative ring at a bundled minimal prime is
injective as a module over the original ring. -/
@[stacks 08XT]
instance injective_localizationAtPrime
    {R : Type u} [CommRing R] [IsReduced R] (p : minimalPrimes R) :
    Module.Injective R (Localization.AtPrime p.1) := sorry

end minimalPrimes
