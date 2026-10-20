/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.Basic

@[expose] public section

/-!
# Composition of Relative Global Complete Intersections

This leaf owns composition for the intrinsic relative-global-complete-
intersection algebra predicate.

@stack 00SZ
-/

universe u v w

namespace Algebra

namespace IsRelativeGlobalCompleteIntersection

variable {R : Type u} {S : Type v} {S' : Type w}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']

/-- Lemma 10.136.17 (2): relative global complete intersections are stable
under composition. -/
@[stacks 00SZ "composition of relative global complete intersections"]
theorem comp (hRS : IsRelativeGlobalCompleteIntersection R S)
    (hSS' : IsRelativeGlobalCompleteIntersection S S') :
    IsRelativeGlobalCompleteIntersection R S' := sorry

end IsRelativeGlobalCompleteIntersection

end Algebra
