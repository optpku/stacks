/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite.AffineDescent
import StacksCheckRecall

/-!
# Lemma 70.15.1

A finite surjective morphism of algebraic spaces from an affine source forces
the target to be affine.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 70.15.1: if `f : X ⟶ Y` is a finite surjective morphism of algebraic
spaces over a scheme `S` and `X` is affine, then `Y` is affine. -/
@[stacks 07VS] #check
  (AlgebraicGeometry.AlgebraicSpace.IsAffine.of_isFinite_surjective :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [Surjective f] [IsFinite f] [IsAffine X], IsAffine Y)
