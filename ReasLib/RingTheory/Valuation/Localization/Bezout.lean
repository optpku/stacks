/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Bezout
public import ReasLib.RingTheory.Valuation.Localization
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Bézout localizations

@stack 0AST

This leaf keeps localization of Bézout rings separate from the valuation-ring
localization support.  The prime-local valuation-ring conclusion is exposed as
a theorem, because the source ring is an essential mathematical input and
cannot be inferred from the target localization alone.
-/

universe u v

namespace IsBezout

/-- Lemma 15.125.7: a commutative Bézout ring remains Bézout after localization. -/
@[stacks 0AST "Lemma 15.125.7, Bézout localization"]
theorem localization
    (A : Type u) [CommRing A] [IsBezout A] (S : Submonoid A)
    (B : Type v) [CommRing B] [Algebra A B] [IsLocalization S B] :
    IsBezout B := sorry
-- Proof strategy: represent generators of a finitely generated ideal of `B`
-- by fractions over `A`, clear their finitely many denominators, and apply the
-- Bezout property to the resulting finitely generated ideal of numerators.
-- Mapping its generator back to `B` generates the original ideal.

/-- Lemma 15.125.7: a prime localization of a Bézout domain is a valuation ring. -/
@[stacks 0AST "Lemma 15.125.7, prime localization valuation ring"]
theorem localizationAtPrime_valuationRing
    (A : Type u) [CommRing A] [IsDomain A] [IsBezout A]
    (p : Ideal A) [p.IsPrime] :
    ValuationRing (Localization.AtPrime p) := sorry
-- Proof strategy: install the canonical local-domain structure on
-- `Localization.AtPrime p`, apply `IsBezout.localization`, and conclude with
-- `ValuationRing.iff_local_bezout_domain`.

end IsBezout
