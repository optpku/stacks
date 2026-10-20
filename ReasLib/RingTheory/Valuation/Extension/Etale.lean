module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import ReasLib.RingTheory.Valuation.Extension
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Etale branches of valuation rings

An etale algebra localized at a prime over the source maximal ideal is again a valuation-ring
extension, and its induced value-group map is bijective.

@stack 0ASJ
-/

open IsLocalRing

universe u v

namespace Algebra.Etale

/-- The branch localization of an etale algebra over a valuation ring is a domain. This support
fact is a theorem rather than a global instance because the base valuation ring is not determined
by the target localization type. -/
@[stacks 0ASJ "domain structure on an etale valuation branch"]
theorem localizationAtPrime_isDomain
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
    {B : Type v} [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (m : Ideal B) [m.IsPrime] [m.LiesOver (maximalIdeal A)] :
    IsDomain (Localization.AtPrime m) := sorry
-- Proof strategy: valuation rings have weak dimension at most one; transfer
-- this bound across the etale map and apply the local weak-dimension
-- characterization at `m` to obtain the domain component.

/-- The branch localization of an etale algebra over a valuation ring is a valuation ring. -/
@[stacks 0ASJ "valuation-ring structure on an etale branch"]
theorem localizationAtPrime_valuationRing
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
    {B : Type v} [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (m : Ideal B) [m.IsPrime] [m.LiesOver (maximalIdeal A)]
    [IsDomain (Localization.AtPrime m)] :
    ValuationRing (Localization.AtPrime m) := sorry
-- Proof strategy: use etale invariance of weak dimension and the equivalence
-- between weak dimension at most one and valuation-ring prime localizations;
-- evaluate it at `m`.

/-- Lemma 15.124.5 (1) (0ASJ): localizing an etale algebra at a prime over the source maximal
ideal gives an extension of valuation rings. -/
@[stacks 0ASJ "Lemma 15.124.5 (1): etale branch extension of valuation rings"]
theorem localizationAtPrime_isExtensionOfValuationRings
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
    {B : Type v} [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (m : Ideal B) [m.IsPrime] [m.LiesOver (maximalIdeal A)] :
    letI : IsDomain (Localization.AtPrime m) := localizationAtPrime_isDomain A m
    letI : ValuationRing (Localization.AtPrime m) := localizationAtPrime_valuationRing A m
    IsExtensionOfValuationRings A (Localization.AtPrime m) := sorry
-- Proof strategy: the etale lying-over hypothesis identifies the image of
-- `maximalIdeal A` with the maximal ideal of `Localization.AtPrime m`, giving
-- locality.  Flatness of the etale localization and the target domain give
-- injectivity of the algebra map; package both fields of the extension class.

/-- Lemma 15.124.5 (2) (0ASJ): the localized etale valuation-ring extension is weakly
unramified. -/
@[stacks 0ASJ "Lemma 15.124.5 (2): etale branch is weakly unramified"]
theorem localizationAtPrime_weaklyUnramified
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
    {B : Type v} [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (m : Ideal B) [m.IsPrime] [m.LiesOver (maximalIdeal A)] :
    letI : IsDomain (Localization.AtPrime m) := localizationAtPrime_isDomain A m
    letI : ValuationRing (Localization.AtPrime m) := localizationAtPrime_valuationRing A m
    letI : IsExtensionOfValuationRings A (Localization.AtPrime m) :=
      localizationAtPrime_isExtensionOfValuationRings A m
    IsExtensionOfValuationRings.WeaklyUnramified A (Localization.AtPrime m) := sorry
-- Proof strategy: injectivity of the value-group map follows from its strict
-- monotonicity.  For surjectivity, represent a nonzero target value by a local
-- element; finite etale approximation and finiteness of the value-group quotient
-- give a positive power equal to a source value up to a unit.  Apply the
-- height-one power-descent theorem and cancel that power in the ordered value
-- group.  Handle zero separately.

end Algebra.Etale

end
