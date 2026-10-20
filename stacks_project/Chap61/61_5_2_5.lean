/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap61.«61_5_2_5_WLocalization»
import StacksCheckRecall

@[expose] public section

universe u

/- 61.5.2.5: for a ring `A`, writing `I(A)` for the directed poset of finite
subsets of `A` and `A_E` for the stage algebra `stage A E`, the w-localization
is the filtered colimit `A_w = colim_{E ∈ Finset A} A_E`. -/
@[stacks 0973] #check (Algebra.WLocalHull.wLocalization :
  ∀ (A : Type u) [CommRing A], Type u)

#check (Algebra.WLocalHull.stage : ∀ (A : Type u) [CommRing A], Finset A → Type u)

#check (Algebra.WLocalHull.of :
  ∀ (A : Type u) [CommRing A] (E : Finset A),
    Algebra.WLocalHull.stage A E →+* Algebra.WLocalHull.wLocalization A)
