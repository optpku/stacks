/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.WellNighAffine
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Morphism.Affine

/-!
# Permanence of well-nigh affine algebraic stacks

A well-nigh affine algebraic stack that is an algebraic space is affine. An
algebraic stack affine over a well-nigh affine algebraic stack is itself
well-nigh affine.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsWellNighAffine

/-- An algebraic space equivalent to a well-nigh affine algebraic stack is
affine. -/
@[stacks 0DUN]
theorem isAffine {S : Scheme.{u}} {X : GroupoidsOver S} {F : AlgebraicSpace S}
    [AlgebraicStack X] [IsWellNighAffine X]
    (hF : Nonempty (X ≌ F.toGroupoids)) : AlgebraicSpace.IsAffine F :=
  sorry

/-- An algebraic stack admitting an affine morphism to a well-nigh affine
algebraic stack is well-nigh affine. -/
@[stacks 0DUN]
theorem of_affine {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] [IsWellNighAffine X] (f : X' ⟶ X)
    [Groupoids.Hom.Affine f] : IsWellNighAffine X' :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsWellNighAffine

namespace AlgebraicGeometry.AlgebraicSpace.IsAffine

/-- A well-nigh affine algebraic space is affine. -/
instance of_isWellNighAffine {S : Scheme.{u}} (X : AlgebraicSpace S)
    [AlgebraicStack.IsWellNighAffine X.toGroupoids] : IsAffine X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsAffine
