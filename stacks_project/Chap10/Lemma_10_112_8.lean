/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RegularLocalRing.Fiber
import StacksCheckRecall

@[expose] public section

/-!
# Regularity Across a Flat Local Homomorphism

@stack 031E
-/

/- Lemma 10.112.8 (Stacks tag `031E`): for a flat local homomorphism of
Noetherian local rings, regularity of the source and of
`S / maximalIdeal R · S` implies regularity of `S`.  The first recall turns
the quotient hypothesis into regularity of the canonical closed fiber; the
second is the flat-local regularity owner. -/

@[stacks 031E "closed-fiber quotient criterion"]
#check @Ideal.Fiber.isRegularLocalRing_of_quotient
@[stacks 031E]
#check @IsRegularLocalRing.of_flat_localHom_of_regular_closedFiber
