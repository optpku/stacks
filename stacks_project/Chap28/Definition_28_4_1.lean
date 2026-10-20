/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.LocalProperty
import StacksCheckRecall

/-!
# Definition 28.4.1

The reusable principal-open locality owner is
`ReasLib.RingTheory.LocalProperty`.
-/

@[expose] public section

universe u

/- Definition 28.4.1: the principal-open locality condition for a commutative-ring property. -/
@[stacks 01OP] #check (RingPropertyIsLocal : (CommRingCat.{u} → Prop) → Prop)

#check (ringPropertyIsLocal_iff :
  ∀ (P : CommRingCat.{u} → Prop),
    RingPropertyIsLocal P ↔
      (∀ (R : CommRingCat.{u}) (f : R),
        P R → P (CommRingCat.of (Localization.Away f))) ∧
      (∀ (R : CommRingCat.{u}) (s : Finset R),
        Ideal.span (s : Set R) = ⊤ →
          (∀ f ∈ s, P (CommRingCat.of (Localization.Away f))) → P R))
