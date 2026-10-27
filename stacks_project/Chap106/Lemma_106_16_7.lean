/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Quasicoherent.TensorReconstruction
public import stacks_project.Chap96.Lemma_96_15_1_Tensor
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open CategoryTheory.Limits
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

/- Lemma 106.16.7. A right exact tensor functor from quasi-coherent modules on a
Noetherian algebraic stack with affine diagonal to modules over a ring, commuting
with direct sums, comes from a unique morphism from the spectrum of that ring. -/
@[stacks 0GRQ] #check
  (AlgebraicGeometry.GroupoidsOver.QCoh.existsUnique_hom_of_rightExactTensor :
    ∀ {X : GroupoidsOver (Spec (.of (ULift.{u} ℤ)))} [AlgebraicStack X]
      [AlgebraicStack.IsNoetherian X]
      [Groupoids.Hom.Affine (diagonal.{u + 1, u, u + 1} X)]
      {U : Over (Spec (.of (ULift.{u} ℤ)))} [IsAffine U.left]
      (F : GroupoidsOver.QCoh X ⥤ ModuleCat.{u} Γ(U.left, ⊤)) [F.Braided]
      [PreservesFiniteColimits F]
      [∀ J : Type u, PreservesColimitsOfShape (Discrete J) F],
      ∃ (f : GroupoidsOver.slice U ⟶ X)
        (t : F ≅ GroupoidsOver.QCoh.tensorPullback f),
        GroupoidsOver.QCoh.IsTensorPullbackIso F t ∧
          ∀ (f' : GroupoidsOver.slice U ⟶ X)
            (t' : F ≅ GroupoidsOver.QCoh.tensorPullback f'),
            GroupoidsOver.QCoh.IsTensorPullbackIso F t' →
              ∃ α : f ⟶ f', t ≪≫ GroupoidsOver.QCoh.tensorPullbackIso α = t')
