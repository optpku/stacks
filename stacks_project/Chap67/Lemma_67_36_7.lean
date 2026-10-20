/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Syntomic.UniversallyOpen
import StacksCheckRecall

/-!
# Syntomic morphisms of algebraic spaces are universally open
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.36.7: A syntomic morphism is universally open. -/
@[stacks 0DF0] #check (AlgebraicGeometry.AlgebraicSpace.UniversallyOpen.of_syntomic :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicGeometry.AlgebraicSpace.Syntomic f],
    AlgebraicGeometry.AlgebraicSpace.UniversallyOpen f)
