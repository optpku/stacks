/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.DividedPowers.Compatibility

@[expose] public section

universe u v

/- Definition 60.4.1: for divided power structures `gamma` on `I` and `delta` on `J`,
the structure `delta` is compatible with `gamma` along `f` when a divided power structure on
`J ⊔ I.map f` makes both the map `f` and the identity of `B` divided-power morphisms. -/
@[stacks 07HK] #check (DividedPowers.IsCompatible :
  {A : Type u} → [CommRing A] → {I : Ideal A} → DividedPowers I →
    {B : Type v} → [CommRing B] → {J : Ideal B} → DividedPowers J →
      (A →+* B) → Prop)

#check DividedPowers.isCompatible_iff
#check DividedPowers.isCompatible_of
