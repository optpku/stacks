/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.LocalRing.Kollar.Criterion
import StacksCheckRecall

/-!
# Kollár's Local-Ring Alternative

Kollár's criterion says that a Noetherian local ring lies in exactly one of four cases:
Artinian, regular of dimension one, depth at least two, or admitting the exceptional finite
extension described by `IsLocalRing.Kollar.HasExceptionalExtension`.

@stack 0BHZ
-/

@[expose] public section

/- Lemma 10.119.2 (Kollár): exactly one of the Artinian, regular dimension-one,
depth-at-least-two, and exceptional finite-extension alternatives holds. -/
@[stacks 0BHZ]
#check @IsLocalRing.Kollar.exactlyOne
