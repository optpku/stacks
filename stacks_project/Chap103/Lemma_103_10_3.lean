/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import stacks_project.Chap96.Lemma_96_12_3_Pullback
public import stacks_project.Chap103.Lemma_103_10_1

/-!
# Pullback of the quasi-coherent right adjoint along a flat morphism

If `f : X ⟶ Y` is a flat morphism of algebraic stacks, then
`LQCohFbc.toQCoh` commutes with pullback: `Q_X ∘ f^* ≅ f^* ∘ Q_Y`.

`LQCohFbc.inverseImage` is restated from Proposition 103.8.1 because that
file cannot be imported with `Lemma_103_10_1` (`projection_isContinuous`
from `Lemma_96_8_1_RingedSite` versus `Lemma_96_11_2_Pullback`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
  [AlgebraicStack X] [AlgebraicStack Y]

namespace LQCohFbc

/-- Pullback `f^* : LQCoh^{fbc}(𝒪_Y) ⥤ LQCoh^{fbc}(𝒪_X)` along a morphism of
algebraic stacks, as the lift of `moduleInverseImage`. -/
def inverseImage (f : X ⟶ Y) : LQCohFbc Y ⥤ LQCohFbc X :=
  (lqcohFbc X).lift (inclusion Y ⋙ moduleInverseImage f) (fun _ ↦ sorry)

/-- The underlying étale functor of `LQCohFbc.inverseImage f` is
`moduleInverseImage f`. -/
theorem inverseImage_comp_inclusion (f : X ⟶ Y) :
    inverseImage f ⋙ inclusion X = inclusion Y ⋙ moduleInverseImage f :=
  sorry

end LQCohFbc

/-- Left-adjoint square comparing quasi-coherent pullback with the inclusion
`QCoh.toLQCohFbc` and étale inverse image on `LQCoh^{fbc}`. -/
def QCoh.toLQCohFbc_pullback (f : X ⟶ Y) :
    QCoh.pullback f ⋙ QCoh.toLQCohFbc X ⟶
      QCoh.toLQCohFbc Y ⋙ LQCohFbc.inverseImage f where
  app G := homMk (𝟙 _)
  naturality := sorry

/-- Induced comparison `f^* Q_Y ⟶ Q_X ∘ f^*` obtained as the mate of
`QCoh.toLQCohFbc_pullback`. -/
def LQCohFbc.toQCoh_pullback (f : X ⟶ Y) :
    LQCohFbc.toQCoh Y ⋙ QCoh.pullback f ⟶
      LQCohFbc.inverseImage f ⋙ LQCohFbc.toQCoh X :=
  mateEquiv (QCoh.toLQCohFbc_isRightAdjoint_toQCoh Y).some
    (QCoh.toLQCohFbc_isRightAdjoint_toQCoh X).some
    (QCoh.toLQCohFbc_pullback f)

/-- For a flat morphism of algebraic stacks, the induced comparison
`f^* Q_Y(F) ⟶ Q_X(f^* F)` is an isomorphism. -/
instance LQCohFbc.toQCoh_pullback_isIso (f : X ⟶ Y) [AlgebraicStack.Flat f] :
    IsIso (LQCohFbc.toQCoh_pullback f) :=
  sorry

/-- Lemma 103.10.3: if `f : X ⟶ Y` is a flat morphism of algebraic stacks,
then `Q_X ∘ f^* = f^* ∘ Q_Y` as functors `LQCohFbc Y ⥤ QCoh X`, where `Q`
is `LQCohFbc.toQCoh` from Lemma 103.10.1, `f^*` on `LQCoh^{fbc}` is
`LQCohFbc.inverseImage`, and `f^*` on `QCoh` is `QCoh.pullback`. -/
@[stacks 0GQJ]
def LQCohFbc.toQCoh_pullbackIso (f : X ⟶ Y) [AlgebraicStack.Flat f] :
    LQCohFbc.inverseImage f ⋙ LQCohFbc.toQCoh X ≅
      LQCohFbc.toQCoh Y ⋙ QCoh.pullback f :=
  (asIso (LQCohFbc.toQCoh_pullback f)).symm

/-- The component of `toQCoh_pullbackIso f` at `F` is the inverse of the
induced map `f^* Q_Y(F) ⟶ Q_X(f^* F)`. -/
theorem LQCohFbc.toQCoh_pullback_hom_app (f : X ⟶ Y) [AlgebraicStack.Flat f]
    (F : LQCohFbc Y) :
    (LQCohFbc.toQCoh_pullbackIso f).hom.app F =
      inv ((LQCohFbc.toQCoh_pullback f).app F) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
