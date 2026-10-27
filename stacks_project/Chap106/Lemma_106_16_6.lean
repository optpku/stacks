/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Quasicoherent.TensorFullyFaithful
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

/- Lemma 106.16.6. An isomorphism of the affine tensor pullback functors of two
morphisms to an algebraic stack with affine diagonal is induced by a 2-arrow. -/
@[stacks 0GRP] #check (AlgebraicGeometry.GroupoidsOver.QCoh.exists_twoArrow_of_tensorIso :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [Groupoids.Hom.Affine (diagonal.{u + 1, u, u + 1} X)]
    {U : Over S} [IsAffine U.left]
    (f1 f2 : GroupoidsOver.slice U ⟶ X)
    (t : GroupoidsOver.QCoh.tensorPullback f1 ≅ GroupoidsOver.QCoh.tensorPullback f2),
    GroupoidsOver.QCoh.IsTensorNatIso t →
      ∃ α : f1 ⟶ f2, t = GroupoidsOver.QCoh.tensorPullbackIso α)
