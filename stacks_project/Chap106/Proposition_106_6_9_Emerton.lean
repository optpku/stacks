/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import stacks_project.Chap106.«106_6_1_1_Object»
public import stacks_project.Chap106.Definition_106_3_3_FirstOrderThickening

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

namespace AlgebraicGeometry.AlgebraicStack.Lift

/-- Proposition 106.6.9 (Emerton). Let `iX : X ⟶ X'` be a first-order
thickening of algebraic stacks. Let `W` be an affine scheme and let
`x : W.toGroupoids ⟶ X` be a smooth morphism. Then there exist an affine
algebraic space `W'`, a morphism `i : W ⟶ W'`, a smooth morphism
`x' : W'.toGroupoids ⟶ X'`, and a 2-cell `α` making the square `W → W'`
over `X → X'` 2-cartesian. -/
@[stacks 0CKI]
theorem exists_affine_smooth_lift {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (iX : X ⟶ X')
    [IsFirstOrderThickening iX] {W : AlgebraicSpace S}
    [AlgebraicSpace.IsAffine W] (x : W.toGroupoids ⟶ X)
    [Groupoids.Hom.Smooth x] :
    ∃ (W' : AlgebraicSpace S) (i : W ⟶ W') (x' : W'.toGroupoids ⟶ X')
      (α : x ≫ iX ≅ AlgebraicSpace.toGroupoids.map i ≫ x'),
      AlgebraicSpace.IsAffine W' ∧ Groupoids.Hom.Smooth x' ∧
        PseudoPullbackCone.IsBilimit
          (⟨W.toGroupoids, x, AlgebraicSpace.toGroupoids.map i, α⟩ :
            PseudoPullbackCone iX x') :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Lift
