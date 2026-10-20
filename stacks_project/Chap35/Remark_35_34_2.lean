/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import stacks_project.Chap35.Definition_35_34_3_DescentData
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits

universe u

variable {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
variable (sq : ChosenPullback f f) (sq₃ : ChosenPullback₃ sq sq sq)
variable (D : AlgebraicGeometry.Scheme.DescentData.Chosen
  (fun _ : PUnit ↦ X) (fun _ ↦ f) (fun _ _ ↦ sq) (fun _ _ _ ↦ sq₃))

/- Remark 35.34.2 (1): the comparison between the two pullbacks of a scheme descent datum
to a chosen pairwise overlap is an isomorphism. -/
@[stacks 02VP] #check
  (AlgebraicGeometry.Scheme.DescentData.Chosen.iso
      (fun _ : PUnit ↦ X) (fun _ ↦ f) (fun _ _ ↦ sq) (fun _ _ _ ↦ sq₃)
      D PUnit.unit PUnit.unit :
    (AlgebraicGeometry.Scheme.overPseudofunctor.map sq.p₁.op.toLoc).toFunctor.obj
          (D.obj PUnit.unit) ≅
      (AlgebraicGeometry.Scheme.overPseudofunctor.map sq.p₂.op.toLoc).toFunctor.obj
          (D.obj PUnit.unit))

/- Remark 35.34.2 (2): the comparison isomorphisms satisfy the cocycle equation after
pullback to a chosen triple overlap. -/
@[stacks 02VP] #check
  (AlgebraicGeometry.Scheme.DescentData.Chosen.cocycle
      (fun _ : PUnit ↦ X) (fun _ ↦ f) (fun _ _ ↦ sq) (fun _ _ _ ↦ sq₃)
      D PUnit.unit PUnit.unit PUnit.unit :
    CategoryTheory.Pseudofunctor.DescentData'.pullHom'
          (fun a b ↦ (AlgebraicGeometry.Scheme.DescentData.Chosen.iso
            (fun _ : PUnit ↦ X) (fun _ ↦ f) (fun _ _ ↦ sq) (fun _ _ _ ↦ sq₃)
            D a b).hom)
          sq₃.p sq₃.p₁ sq₃.p₂ ≫
        CategoryTheory.Pseudofunctor.DescentData'.pullHom'
          (fun a b ↦ (AlgebraicGeometry.Scheme.DescentData.Chosen.iso
            (fun _ : PUnit ↦ X) (fun _ ↦ f) (fun _ _ ↦ sq) (fun _ _ _ ↦ sq₃)
            D a b).hom)
          sq₃.p sq₃.p₂ sq₃.p₃ =
      CategoryTheory.Pseudofunctor.DescentData'.pullHom'
        (fun a b ↦ (AlgebraicGeometry.Scheme.DescentData.Chosen.iso
          (fun _ : PUnit ↦ X) (fun _ ↦ f) (fun _ _ ↦ sq) (fun _ _ _ ↦ sq₃)
          D a b).hom)
        sq₃.p sq₃.p₁ sq₃.p₃)
