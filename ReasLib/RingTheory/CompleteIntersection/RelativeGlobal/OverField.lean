/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CompleteIntersection.OverField
public import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.Basic

@[expose] public section

/-!
# Relative Global Complete Intersections over a Field

@stack 00T5

This leaf records the specialization from the fiberwise relative-global
complete-intersection condition to the absolute global condition when the
base is a field.  It belongs to the relative-global owner and is independent
of the smoothness application where it first occurs.
-/

universe u v

namespace Algebra

namespace IsRelativeGlobalCompleteIntersection

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S]

/-- Lemma 10.137.4, tag `00T5`: over a field, a relative global complete
intersection is a global complete intersection. -/
@[stacks 00T5 "relative global complete intersection over a field"]
theorem isGlobalCompleteIntersection (hS : IsRelativeGlobalCompleteIntersection k S) :
    IsGlobalCompleteIntersection k S := sorry

end IsRelativeGlobalCompleteIntersection

end Algebra
