/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Lift.Affine

/-!
# Affine smooth cartesian lifts along first-order thickenings

A smooth morphism from an affine algebraic space into a first-order thickening
of algebraic stacks lifts to a 2-cartesian square whose thickened source is
affine and whose map to the thickened stack is smooth.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack Bicategory
open scoped Bicategory

universe u

/- Proposition 106.6.9 (Emerton). A smooth morphism from an affine scheme
to an algebraic stack admits an affine smooth cartesian lift along a first-order
thickening of the stack. -/
@[stacks 0CKI] #check (AlgebraicGeometry.AlgebraicStack.Lift.existsAffine :
    ∀ {S : Scheme.{u}} {X X' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] (iX : X ⟶ X')
      [IsFirstOrderThickening iX] {W : AlgebraicSpace S}
      [AlgebraicSpace.IsAffine W] (x : W.toGroupoids ⟶ X)
      [Groupoids.Hom.Smooth x],
    ∃ (W' : AlgebraicSpace S) (i : W ⟶ W') (x' : W'.toGroupoids ⟶ X')
      (α : x ≫ iX ≅ AlgebraicSpace.toGroupoids.map i ≫ x'),
      AlgebraicSpace.IsAffine W' ∧ Groupoids.Hom.Smooth x' ∧
        PseudoPullbackCone.IsBilimit
          (⟨W.toGroupoids, x, AlgebraicSpace.toGroupoids.map i, α⟩ :
            PseudoPullbackCone iX x'))
