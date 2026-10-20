/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Immersion.Local
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 29.3.5: if every point of the source has a target-open neighborhood on which the
restricted morphism is an immersion, then the original morphism is an immersion. -/
@[stacks 0FCZ] #check
  (AlgebraicGeometry.IsImmersion.of_forall_source_exists_morphismRestrict :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X),
      (∀ y : Y, ∃ U : X.Opens, f y ∈ U ∧ AlgebraicGeometry.IsImmersion (f ∣_ U)) →
        AlgebraicGeometry.IsImmersion f)
