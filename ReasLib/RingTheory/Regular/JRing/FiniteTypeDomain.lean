/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Localization.FractionRing.Separable
public import ReasLib.RingTheory.Regular.JRing
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# J-0 transfer for finite type domains

@stack 07PA
@stack 07PB

These two results expose the descent and separable generic ascent directions
under one symmetric namespace.
-/

universe u v

namespace IsJ0Ring.FiniteTypeDomain

/-- The `J-0` property descends along an injective finite type map of domains when the source
ring is Noetherian. This is Lemma 15.47.4. -/
@[stacks 07PA "descent of J-0 along an injective finite type map"]
theorem descend
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsDomain R] [IsDomain S] [Algebra.FiniteType R S] [IsJ0Ring S]
    (h_injective : Function.Injective (algebraMap R S)) :
    IsJ0Ring R := sorry

/-- The `J-0` property ascends along an injective finite type map of domains whose induced
fraction-field extension is separable. This is Lemma 15.47.5. -/
@[stacks 07PB "separable generic ascent of J-0"]
theorem ascend
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain R] [IsDomain S] [Algebra.FiniteType R S] [IsJ0Ring R]
    (h_injective : Function.Injective (algebraMap R S))
    (h_separable :
      FractionRing.isSeparableOf (R := R) (S := S) h_injective) :
    IsJ0Ring S := sorry

end IsJ0Ring.FiniteTypeDomain
