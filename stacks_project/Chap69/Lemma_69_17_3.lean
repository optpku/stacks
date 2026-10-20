/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite.AffineDescent
import StacksCheckRecall

/-!
# Lemma 69.17.3

A finite surjective morphism of algebraic spaces from an affine source onto a
Noetherian target forces the target to be affine.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 69.17.3: A finite surjective morphism from an affine algebraic space
onto a Noetherian algebraic space has affine target. -/
@[stacks 07VP] #check
  (AlgebraicGeometry.AlgebraicSpace.isAffine_of_isFinite_surjective :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
      [IsFinite f] [Surjective f] [IsAffine Y] [IsNoetherian X], IsAffine X)
