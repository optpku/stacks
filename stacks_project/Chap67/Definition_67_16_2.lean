/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticImage
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 67.16.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. The scheme-theoretic image of `f` is the smallest
closed subspace `Z ⊂ Y` through which `f` factors, as supplied by Lemma 67.16.1. -/
@[stacks 082Y] #check (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}, (X ⟶ Y) → (X ⟶ Z) → (Z ⟶ Y) → Prop)

/- A least closed-subspace factorization of `f` is a scheme-theoretic image
factorization, recovering the smallest-closed-subspace wording. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage.of_isLeast_closedSubspace :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      (Z : AlgebraicSpace.ClosedSubspace Y) (toImage : X ⟶ Z.X),
      toImage ≫ Z.ι = f →
        (∀ Z' : AlgebraicSpace.ClosedSubspace Y,
            (∃ toZ' : X ⟶ Z'.X, toZ' ≫ Z'.ι = f) →
              ∃ k : Z.X ⟶ Z'.X, k ≫ Z'.ι = Z.ι) →
          AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage f toImage Z.ι)
