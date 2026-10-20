/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flatness.MittagLeffler
import StacksCheckRecall

@[expose] public section

universe u v

/-!
# Mittag-Leffler modules

Definition 10.88.7: an `R`-module `M` is Mittag-Leffler if the equivalent
conditions of Proposition 10.88.6 hold.  In particular a finitely presented
module is Mittag-Leffler.

The reusable owner is the unbundled property class `Module.MittagLeffler`,
witnessed by a concrete `Module.MittagLeffler.Presentation`.

@stack 059F
-/

/- Definition 10.88.7: an `R`-module is Mittag-Leffler when the equivalent
conditions of Proposition 10.88.6 hold. -/
@[stacks 059F] #check (@Module.MittagLeffler :
  (R : Type u) → (M : Type v) → [Ring R] → [AddCommGroup M] → [Module R M] → Prop)
