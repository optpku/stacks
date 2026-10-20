/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineEtaleCover
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 66.6.1: let `S` be a scheme and `X` an algebraic space over `S`. There exists a
surjective étale morphism `U ⟶ X` where `U` is a disjoint union of affine schemes. We may
in addition assume each of these affines maps into an affine open of `S`. -/
@[stacks 03FX] #check (AlgebraicGeometry.AlgebraicSpace.exists_affineEtaleCover :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    Nonempty (AlgebraicGeometry.AlgebraicSpace.AffineEtaleCover.{u, u} X))
