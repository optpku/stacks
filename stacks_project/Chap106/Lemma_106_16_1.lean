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

namespace AlgebraicGeometry.AlgebraicStack

namespace Coh

variable {S : Scheme.{u}} {X : GroupoidsOver S}
variable [AlgebraicStack X] [IsLocallyNoetherian X]

/-- Tensor product of coherent modules, computed as the quasi-coherent tensor
of their images under `qCohLift`. -/
def tensor (A B : Coh X) : Coh X where
  obj := (QCoh.tensor (qCohLift.obj A) (qCohLift.obj B)).obj
  property := sorry

/-- The image of `tensor A B` under `qCohLift` is isomorphic to the
quasi-coherent tensor of the images of `A` and `B`. -/
theorem tensor_qCohLift (A B : Coh X) :
    Nonempty
      (qCohLift.obj (tensor A B) ≅ QCoh.tensor (qCohLift.obj A) (qCohLift.obj B)) :=
  sorry

end Coh

/-- Lemma 106.16.1. Let `X` and `Y` be Noetherian algebraic stacks. Any right
exact tensor functor `F : Coh X ⥤ Coh Y` extends uniquely to a right exact
tensor functor `G : QCoh X ⥤ QCoh Y` commuting with all colimits. -/
@[stacks 0GRJ]
theorem existsUnique_extend_rightExactTensor
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [IsNoetherian X] [AlgebraicStack Y] [IsNoetherian Y]
    (F : Coh X ⥤ Coh Y) [PreservesFiniteColimits F]
    (h_tensor : ∀ A B : Coh X,
      Nonempty (F.obj (Coh.tensor A B) ≅ Coh.tensor (F.obj A) (F.obj B))) :
    ∃ G : QCoh X ⥤ QCoh Y,
      PreservesColimitsOfSize.{u, u} G ∧
        Nonempty ((Coh.qCohLift : Coh X ⥤ QCoh X) ⋙ G ≅
          F ⋙ (Coh.qCohLift : Coh Y ⥤ QCoh Y)) ∧
        (∀ A B : QCoh X,
          Nonempty (G.obj (QCoh.tensor A B) ≅ QCoh.tensor (G.obj A) (G.obj B))) ∧
        ∀ (G' : QCoh X ⥤ QCoh Y),
          PreservesFilteredColimitsOfSize.{u, u} G' →
            Nonempty ((Coh.qCohLift : Coh X ⥤ QCoh X) ⋙ G' ≅
              F ⋙ (Coh.qCohLift : Coh Y ⥤ QCoh Y)) →
            Nonempty (G ≅ G') :=
  sorry

end AlgebraicGeometry.AlgebraicStack

