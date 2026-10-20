/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Henselian
public import ReasLib.Algebra.Homology.DerivedCategory.Completeness
import Mathlib.Tactic.CrossRefAttribute

/-!
# Henselian pairs from derived completeness

This file records the ring-level Henselian consequence of derived completeness with respect to an
ideal.

@stack 0G3H
-/

@[expose] public section

universe u

namespace ModuleCat.IsDerivedCompleteWithRespectTo

variable {A : Type u} [CommRing A] {I : Ideal A}

/-- Lemma 15.94.10 (Stacks `0G3H`): a ring derived complete with respect to `I` forms a
Henselian pair with `I`. -/
@[stacks 0G3H "derived completeness gives a Henselian pair"]
theorem henselianRing
    (hA : (ModuleCat.of A A).IsDerivedCompleteWithRespectTo I) :
    HenselianRing A I := sorry

end ModuleCat.IsDerivedCompleteWithRespectTo
