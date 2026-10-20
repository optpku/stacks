/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.39.17

@stack 00HR
-/

-- Declarations for this item will be appended below by the statement pipeline.

/-
Lemma 10.39.17: a flat local ring homomorphism between local rings is faithfully flat.

Layering for this item:
* source-facing: a flat local ring homomorphism of local rings is faithfully flat;
* core/canonical owner: `Module.FaithfullyFlat.of_flat_of_isLocalHom`;
* bridge/view: the ring-hom statement is the canonical algebraized view for `algebraMap`.
-/
@[stacks 00HR]
#check @Module.FaithfullyFlat.of_flat_of_isLocalHom
