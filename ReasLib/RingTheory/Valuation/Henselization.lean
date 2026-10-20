/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Henselian.Henselization
public import ReasLib.RingTheory.Henselian.StrictHenselization
public import ReasLib.RingTheory.Valuation.Extension
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Henselizations of valuation rings

@stack 0ASK

This leaf owns the valuation-ring instances and weakly-unramified maps in a
henselization tower.  The henselization objects remain the primitive inputs;
the domain, valuation-ring, extension, and value-group statements are named
derived API.
-/

universe u

open IsExtensionOfValuationRings

namespace ValuationRing.Henselization

/-- A henselization of a valuation ring is a domain. -/
@[stacks 0ASK "henselization domain structure"]
theorem domain_of_henselization
    {A Ah : Type u}
    [hCommA : CommRing A] [hDomA : IsDomain A] [hValA : ValuationRing A]
    [hCommAh : CommRing Ah] [hAlg : Algebra A Ah]
    [hHensel : IsHenselizationOf A Ah] :
    IsDomain Ah := sorry
-- Proof strategy: use the filtered-colimit presentation of a henselization by
-- pointed etale neighborhoods.  Select the local branch over the closed point,
-- apply the etale-branch domain theorem stagewise, and use stability of domains
-- under the injective filtered transition maps.

/-- A henselization of a valuation ring is again a valuation ring. -/
@[stacks 0ASK "henselization valuation-ring structure"]
theorem valuationRing_of_henselization
    {A Ah : Type u}
    [hCommA : CommRing A] [hDomA : IsDomain A] [hValA : ValuationRing A]
    [hCommAh : CommRing Ah] [hAlg : Algebra A Ah]
    [hHensel : IsHenselizationOf A Ah] [hDomAh : IsDomain Ah] :
    ValuationRing Ah := sorry
-- Proof strategy: present `Ah` as the directed colimit of its local etale
-- branches, use `Algebra.Etale.localizationAtPrime_valuationRing` at every
-- stage, and apply the directed-colimit valuation-ring owner.

/-- The henselization map is an extension of valuation rings. -/
@[stacks 0ASK "henselization extension of valuation rings"]
theorem extension_of_henselization
    {A Ah : Type u}
    [hCommA : CommRing A] [hDomA : IsDomain A] [hValA : ValuationRing A]
    [hCommAh : CommRing Ah] [hAlg : Algebra A Ah]
    [hHensel : IsHenselizationOf A Ah]
    [hDomAh : IsDomain Ah] [hValAh : ValuationRing Ah] :
    IsExtensionOfValuationRings A Ah := sorry
-- Proof strategy: `IsHenselizationOf` supplies locality; faithful flatness of
-- the henselization map supplies injectivity.  Package these as the two fields
-- of `IsExtensionOfValuationRings`.

/-- Install the canonical extension-of-valuation-rings instance on a henselization. -/
@[stacks 0ASK "valuation extension structure on a Henselization"]
instance extension_instance
    {A Ah : Type u}
    [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]
    [IsDomain Ah] [ValuationRing Ah] :
    IsExtensionOfValuationRings A Ah :=
  extension_of_henselization (A := A) (Ah := Ah)

/-- Lemma 15.124.6 (1): the henselization map is weakly unramified. -/
@[stacks 0ASK "Lemma 15.124.6 (1), henselization weakly unramified"]
theorem weaklyUnramified
    {A Ah : Type u}
    [hCommA : CommRing A] [hDomA : IsDomain A] [hValA : ValuationRing A]
    [hCommAh : CommRing Ah] [hAlg : Algebra A Ah]
    [hHensel : IsHenselizationOf A Ah]
    [hDomAh : IsDomain Ah] [hValAh : ValuationRing Ah] :
    WeaklyUnramified A Ah := sorry
-- Proof strategy: injectivity of the value-group map is automatic.  Represent
-- a target value by an element of `FractionRing Ah`, descend its numerator and
-- denominator to one pointed etale stage of the henselization, and use the
-- stagewise etale weak-unramified theorem to obtain a source value preimage.

end ValuationRing.Henselization

namespace ValuationRing.StrictHenselization

/-- A strict henselization of a valuation ring is a domain. -/
@[stacks 0ASK "strict henselization domain structure"]
theorem domain_of_strictHenselization
    {A Ash : Type u}
    [hCommA : CommRing A] [hDomA : IsDomain A] [hValA : ValuationRing A]
    [hCommAsh : CommRing Ash] [hAlg : Algebra A Ash]
    [hStrict : IsStrictHenselizationOf A Ash] :
    IsDomain Ash := sorry
-- Proof strategy: use the strict-henselization filtered-colimit presentation by
-- pointed etale neighborhoods and the stagewise etale branch domain theorem,
-- then pass domainhood through the directed colimit.

/-- A strict henselization over a valuation ring is again a valuation ring. -/
@[stacks 0ASK "strict henselization valuation-ring structure"]
theorem valuationRing_of_strictHenselization
    {A Ash : Type u}
    [hCommA : CommRing A] [hDomA : IsDomain A] [hValA : ValuationRing A]
    [hCommAsh : CommRing Ash] [hAlg : Algebra A Ash]
    [hStrict : IsStrictHenselizationOf A Ash] [hDomAsh : IsDomain Ash] :
    ValuationRing Ash := sorry
-- Proof strategy: every pointed etale branch is a valuation ring; combine the
-- strict-henselization colimit presentation with the directed-colimit
-- valuation-ring theorem.

/-- The strict henselization map is an extension of valuation rings. -/
@[stacks 0ASK "strict henselization extension of valuation rings"]
theorem extension_of_strictHenselization
    {A Ash : Type u}
    [hCommA : CommRing A] [hDomA : IsDomain A] [hValA : ValuationRing A]
    [hCommAsh : CommRing Ash] [hAlg : Algebra A Ash]
    [hStrict : IsStrictHenselizationOf A Ash]
    [hDomAsh : IsDomain Ash] [hValAsh : ValuationRing Ash] :
    IsExtensionOfValuationRings A Ash := sorry
-- Proof strategy: use the local-map field of `IsStrictHenselizationOf` and
-- injectivity of its faithfully flat algebra map, then construct the extension
-- class.

/-- Install the canonical extension-of-valuation-rings instance on a strict henselization. -/
@[stacks 0ASK "valuation extension structure on a strict Henselization"]
instance extension_instance
    {A Ash : Type u}
    [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]
    [IsDomain Ash] [ValuationRing Ash] :
    IsExtensionOfValuationRings A Ash :=
  extension_of_strictHenselization (A := A) (Ash := Ash)

/-- Lemma 15.124.6 (2): the strict henselization map is weakly unramified. -/
@[stacks 0ASK "Lemma 15.124.6 (2), strict henselization weakly unramified"]
theorem weaklyUnramified
    {A Ash : Type u}
    [hCommA : CommRing A] [hDomA : IsDomain A] [hValA : ValuationRing A]
    [hCommAsh : CommRing Ash] [hAlg : Algebra A Ash]
    [hStrict : IsStrictHenselizationOf A Ash]
    [hDomAsh : IsDomain Ash] [hValAsh : ValuationRing Ash] :
    WeaklyUnramified A Ash := sorry
-- Proof strategy: reduce to surjectivity of the value-group map, descend a
-- representative target fraction to a pointed etale stage of the strict
-- henselization, and apply etale weak unramifiedness at that stage.

/-- Lemma 15.124.6 (3): the two maps in the henselization tower are weakly unramified. -/
@[stacks 0ASK "Lemma 15.124.6 (3), henselization tower"]
theorem tower_weaklyUnramified
    {A Ah Ash : Type u}
    [hCommA : CommRing A] [hDomA : IsDomain A] [hValA : ValuationRing A]
    [hCommAh : CommRing Ah] [hAlgAh : Algebra A Ah]
    [hHensel : IsHenselizationOf A Ah]
    [hCommAsh : CommRing Ash] [hAlgAsh : Algebra Ah Ash]
    [hStrict : IsStrictHenselizationOf Ah Ash]
    [hDomAh : IsDomain Ah] [hValAh : ValuationRing Ah]
    [hDomAsh : IsDomain Ash] [hValAsh : ValuationRing Ash] :
    WeaklyUnramified A Ah ∧ WeaklyUnramified Ah Ash := sorry
-- Proof strategy: apply `ValuationRing.Henselization.weaklyUnramified` to
-- `A → Ah` and `ValuationRing.StrictHenselization.weaklyUnramified` to
-- `Ah → Ash`, then pair the two propositions.

end ValuationRing.StrictHenselization
