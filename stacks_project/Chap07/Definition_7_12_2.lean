/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Canonical.Subcanonical
import StacksCheckRecall

@[expose] public section

universe u v

variable {C : Type u} [CategoryTheory.Category.{v} C]

/- Definition 7.12.2: the topology on a site C is weaker than the canonical
topology, or subcanonical, when every covering is a universal effective
epimorphism. -/
@[stacks 00WQ] #check
  (CategoryTheory.GrothendieckTopology.subcanonical_iff_forall_cover_isUniversallyEffectiveEpimorphic :
    ∀ (J : CategoryTheory.GrothendieckTopology C),
      J.Subcanonical ↔
        ∀ {X : C} (S : CategoryTheory.Sieve X),
          S ∈ J X → S.IsUniversallyEffectiveEpimorphic)
