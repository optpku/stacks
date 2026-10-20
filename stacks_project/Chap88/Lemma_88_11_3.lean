/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.FiniteType.BaseChange
import StacksCheckRecall

/-!
# Adic topologically finite type arrows of WAdm^{adic*} are stable under base change
-/

@[expose] public section

universe u

open TopologicalRing RingHom

/- Lemma 88.11.3: Consider the property `P` on arrows of `WAdm^{adic*}` defined
in Lemma 88.11.1, namely `fun φ ↦ φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType`.
Then `P` is stable under base change as defined in Formal Spaces,
Remark 87.21.8: `P (algebraMap B A)` implies `P (includeRight B A C)` for the
completed tensor product. -/
@[stacks 0GBY] #check
  (TopologicalRing.IsAdicStarRing.isStableUnderBaseChange_isAdicHom_and_topologicallyOfFiniteType :
    TopologicalRing.IsAdicStarRing.IsLocalMorphismProperty.IsStableUnderBaseChange
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [TopologicalRing.IsAdicStarRing A]
        [CommRing B] [TopologicalSpace B] [TopologicalRing.IsAdicStarRing B]
        (φ : B →+* A) ↦ φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType)
