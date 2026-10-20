/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.Reduced
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 74.9.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. If `f` is flat and surjective and `X` is reduced, then `Y` is
reduced. -/
@[stacks 06MI] #check (AlgebraicGeometry.AlgebraicSpace.Flat.isReduced_of_surjective :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicSpace.Flat f] [AlgebraicSpace.Surjective f] [AlgebraicSpace.IsReduced X],
    AlgebraicSpace.IsReduced Y)
