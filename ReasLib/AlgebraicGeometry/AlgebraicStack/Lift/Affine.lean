/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FirstOrderThickening
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit

/-!
# Affine smooth lifts along first-order thickenings

A smooth morphism from an affine algebraic space to an algebraic stack admits
an affine smooth cartesian lift along a first-order thickening of that stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Lift

/-- A smooth morphism from an affine algebraic space to an algebraic stack
admits an affine smooth lift along a first-order thickening of the stack,
with the resulting square 2-cartesian. -/
@[stacks 0CKI]
theorem existsAffine {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (iX : X ⟶ X')
    [IsFirstOrderThickening iX] {W : AlgebraicSpace S}
    [AlgebraicSpace.IsAffine W] (x : W.toGroupoids ⟶ X)
    [Groupoids.Hom.Smooth x] :
    ∃ (W' : AlgebraicSpace S) (i : W ⟶ W') (x' : W'.toGroupoids ⟶ X')
      (α : x ≫ iX ≅ AlgebraicSpace.toGroupoids.map i ≫ x'),
      AlgebraicSpace.IsAffine W' ∧ Groupoids.Hom.Smooth x' ∧
        PseudoPullbackCone.IsBilimit
          (⟨W.toGroupoids, x, AlgebraicSpace.toGroupoids.map i, α⟩ :
            PseudoPullbackCone iX x') := sorry

end AlgebraicGeometry.AlgebraicStack.Lift
