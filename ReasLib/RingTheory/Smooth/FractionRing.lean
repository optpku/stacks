/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.FieldTheory.Separable.FormallySmooth
public import ReasLib.RingTheory.Localization.FractionRing.Separable
public import ReasLib.RingTheory.Smooth.Localization

/-!
# Smoothness at generic points and fraction fields

This leaf relates smoothness at the generic point of a domain to formal
smoothness and separability of its induced fraction-field extension.

@stack 07ND
-/

@[expose] public section

namespace FractionRing

universe u v

/-- Generic-point smoothness of a domain algebra is formal smoothness of its
fraction ring over the original base. -/
@[stacks 07ND "generic-point smoothness and the fraction ring"]
theorem isSmoothAt_bot_iff_formallySmooth
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S] :
    Algebra.IsSmoothAt R (⊥ : Ideal S) ↔ Algebra.FormallySmooth R (FractionRing S) := sorry

/-- Formal smoothness of the fraction ring of an injective domain algebra is
equivalent to separability of the induced fraction-field extension. -/
@[stacks 07ND "formal smoothness and separable fraction-field extensions"]
theorem formallySmooth_iff_isSeparable
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] (hinj : Function.Injective (algebraMap R S)) :
    Algebra.FormallySmooth R (FractionRing S) ↔
      FractionRing.isSeparableOf hinj := sorry

/-- Lemma 10.140.9, tag `07ND`: for an injective finite-type map of domains,
smoothness at the generic point is equivalent to separability of the induced
fraction-field extension. -/
@[stacks 07ND]
theorem isSmoothAt_bot_iff_isSeparable
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] [Algebra.FiniteType R S]
    (hinj : Function.Injective (algebraMap R S)) :
    Algebra.IsSmoothAt R (⊥ : Ideal S) ↔
      FractionRing.isSeparableOf hinj := sorry

end FractionRing
