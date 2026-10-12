/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Ideal.MinimalPrime.Localization

/-!
# Geometric Reducedness at Minimal Primes

This leaf owns the local-to-global criterion for a geometrically reduced
algebra over a field.  The criterion is expressed using the canonical
localizations at minimal primes, rather than an auxiliary product embedding.
-/

@[expose] public section

universe u v

namespace Algebra.IsGeometricallyReduced

section

variable {S : Type v} [CommRing S]

/-- A reduced algebra over a field is geometrically reduced when its
localizations at all minimal primes are geometrically reduced. -/
@[stacks 07K2]
theorem of_forall_minimalPrimes_localization
    {k : Type u} [Field k] [Algebra k S]
    [IsReduced S]
    (hlocal : ∀ p : minimalPrimes S,
      Algebra.IsGeometricallyReduced k (Localization.AtPrime p.1)) :
    Algebra.IsGeometricallyReduced k S := sorry

/-- Explicit-hypothesis form of `of_forall_minimalPrimes_localization`; use this bridge when
reducedness is available as a proposition value rather than an installed instance. -/
@[stacks 07K2 "explicit reducedness bridge"]
theorem of_forall_minimalPrimes_localization_of
    {k : Type u} [Field k] [Algebra k S]
    (hS : IsReduced S)
    (hlocal : ∀ p : minimalPrimes S,
      Algebra.IsGeometricallyReduced k (Localization.AtPrime p.1)) :
    Algebra.IsGeometricallyReduced k S := sorry

end

end Algebra.IsGeometricallyReduced
