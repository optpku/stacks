/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import stacks_project.Chap96.Lemma_96_15_1_Tensor
public import stacks_project.Chap101.Definition_101_8_1_Noetherian
public import stacks_project.Chap103.Lemma_103_17_5_Abelian

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Quasicoherent.FppfTensorFunctor
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Coherent.Tensor
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Coherent.TensorExtension

/-!
# Unique extension of right exact tensor functors from Coh to QCoh

A right exact tensor functor on coherent modules of Noetherian algebraic
stacks extends uniquely to a colimit-preserving right exact tensor functor
on quasi-coherent modules.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open CategoryTheory.Limits GroupoidsOver

noncomputable section

universe u

/- Lemma 106.16.1. Right exact tensor functors on coherent modules extend
uniquely to colimit-preserving tensor functors on quasi-coherent modules. -/
@[stacks 0GRJ] #check (AlgebraicGeometry.AlgebraicStack.existsUnique_extend_rightExactTensor :
  ∀ {S₁ S₂ : Scheme.{u}} {X : GroupoidsOver S₁} {Y : GroupoidsOver S₂}
    [AlgebraicStack X] [IsNoetherian X] [AlgebraicStack Y] [IsNoetherian Y]
    (F : Coh X ⥤ Coh Y) [PreservesFiniteColimits F]
    (T : Coh.tensorBifunctor X ⋙ F ≅ Functor.prod F F ⋙ Coh.tensorBifunctor Y),
    ∃ G : QCoh X ⥤ QCoh Y,
      PreservesColimitsOfSize.{u, u} G ∧
        ∃ (e : (Coh.toQCoh : Coh X ⥤ QCoh X) ⋙ G ≅
            F ⋙ (Coh.toQCoh : Coh Y ⥤ QCoh Y))
          (U : QCoh.Fppf.tensorBifunctor X ⋙ G ≅
            Functor.prod G G ⋙ QCoh.Fppf.tensorBifunctor Y),
          (∀ A B : Coh X,
            U.hom.app (Coh.toQCoh.obj A, Coh.toQCoh.obj B) ≫
                QCoh.Fppf.tensorMap (e.hom.app A) (e.hom.app B) =
              G.map (Coh.tensor_toQCohIso A B).inv ≫
                e.hom.app (Coh.tensor A B) ≫
                Coh.toQCoh.map (T.hom.app (A, B)) ≫
                (Coh.tensor_toQCohIso (F.obj A) (F.obj B)).hom) ∧
          ∀ G' : QCoh X ⥤ QCoh Y,
            PreservesFilteredColimitsOfSize.{u, u} G' →
              Nonempty ((Coh.toQCoh : Coh X ⥤ QCoh X) ⋙ G' ≅
                F ⋙ (Coh.toQCoh : Coh Y ⥤ QCoh Y)) →
              Nonempty (G ≅ G'))
