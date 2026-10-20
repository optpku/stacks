/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.FiniteType.Reduction.BaseChange
import StacksCheckRecall

/-!
# Finite type on reductions is stable under completed base change
-/

@[expose] public section

universe u

open TopologicalRing RingHom

/- Lemma 88.12.2: Consider the property `P` on arrows of `WAdm^count` defined
in Lemma 88.12.1. Then `P` is stable under base change in the sense of
Situation 87.21.6. -/
@[stacks 0GC3] #check (TopologicalRing.isStableUnderBaseChange_isFiniteTypeOnReduction :
    TopologicalRing.IsLocalMorphismProperty.IsStableUnderBaseChange
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
        [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
        (φ : B →+* A) ↦ φ.IsFiniteTypeOnReduction)
