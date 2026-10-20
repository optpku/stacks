/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.Basic
public import ReasLib.RingTheory.RingHom.Syntomic.Basic

@[expose] public section

/-!
# Syntomicity of Relative Global Complete Intersections

This leaf records the bridge from the intrinsic relative-global-complete-
intersection algebra predicate to the ring-hom syntomic predicate.

@stack 00SW
-/

universe u v

namespace Algebra

namespace IsRelativeGlobalCompleteIntersection

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Lemma 10.136.13: a relative global complete-intersection `R`-algebra is
syntomic over `R`. -/
@[stacks 00SW "relative global complete intersections are syntomic"]
theorem syntomic (hS : IsRelativeGlobalCompleteIntersection R S) :
    (algebraMap R S).Syntomic := sorry

end IsRelativeGlobalCompleteIntersection

end Algebra
