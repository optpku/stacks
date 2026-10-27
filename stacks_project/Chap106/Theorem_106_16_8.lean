/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Coherent.TensorReconstruction
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open CategoryTheory.Functor CategoryTheory.Limits FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

/- Theorem 106.16.8. A right exact tensor functor from coherent modules on a
Noetherian algebraic stack with affine diagonal to finite modules over a
Noetherian ring comes from an essentially unique absolute morphism. -/
@[stacks 0GRR] #check
  (AlgebraicGeometry.AlgebraicStack.Coh.existsUnique_hom_of_rightExactTensor :
    ∀ {X : GroupoidsOver (Spec (.of (ULift.{u} ℤ)))} [AlgebraicStack X]
    [IsNoetherian X]
    [Groupoids.Hom.Affine (diagonal.{u + 1, u, u + 1} X)]
    {U : Over (Spec (.of (ULift.{u} ℤ)))} [IsAffine U.left] [AlgebraicGeometry.IsNoetherian U.left]
    (F : AlgebraicGeometry.AlgebraicStack.Coh X ⥤ FGModuleCat.{u} Γ(U.left, ⊤))
    [F.Braided] [PreservesFiniteColimits F],
    ∃ (f : GroupoidsOver.slice U ⟶ X)
      (t : F ⋙ forget₂ (FGModuleCat.{u} Γ(U.left, ⊤))
            (ModuleCat.{u} Γ(U.left, ⊤)) ≅
          AlgebraicGeometry.AlgebraicStack.Coh.toQCoh ⋙ GroupoidsOver.QCoh.tensorPullback f),
      AlgebraicGeometry.AlgebraicStack.Coh.IsTensorPullbackCohIso F t ∧
        ∀ (f' : GroupoidsOver.slice U ⟶ X)
          (t' : F ⋙ forget₂ (FGModuleCat.{u} Γ(U.left, ⊤))
              (ModuleCat.{u} Γ(U.left, ⊤)) ≅
            AlgebraicGeometry.AlgebraicStack.Coh.toQCoh ⋙ GroupoidsOver.QCoh.tensorPullback f'),
          AlgebraicGeometry.AlgebraicStack.Coh.IsTensorPullbackCohIso F t' →
            ∃ α : f ⟶ f',
              t ≪≫ isoWhiskerLeft AlgebraicGeometry.AlgebraicStack.Coh.toQCoh (GroupoidsOver.QCoh.tensorPullbackIso α) = t')
