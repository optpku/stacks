/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Ample.Relative.Descent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicSpace CategoryTheory Limits MonoidalCategory

universe u v

/- Lemma 74.13.1: relative ampleness of an invertible module on a morphism of algebraic
spaces is equivalent to relative ampleness of every pullback along an fpqc covering of
the target. -/
@[stacks 0D3C] #check
  (AlgebraicGeometry.AlgebraicSpace.RelativelyAmple.iff_forall_baseChange_of_fpqcCovering :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (L : X.Modules)
      [isInvertibleObject L] {ι : Type v} (family : ι → Over Y),
      FpqcCovering family →
        (RelativelyAmple f L ↔
          ∀ i : ι, RelativelyAmple (pullback.snd f (family i).hom)
            ((Modules.pullback (pullback.fst f (family i).hom)).obj L)))
