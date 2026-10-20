/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import stacks_project.Chap74.Definition_74_22_3_DescentData
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits

universe u v

/- Remark 74.22.4 (1): the pairwise comparison maps of algebraic-space descent data
are isomorphisms pr₀* Vᵢ ≅ pr₁* Vⱼ of algebraic spaces over the chosen pairwise
overlaps Xᵢ ×_X Xⱼ. -/
@[stacks 0ADJ] #check
  (AlgebraicGeometry.AlgebraicSpace.DescentData.Chosen.iso :
    ∀ {I : Type v} {S : AlgebraicGeometry.Scheme.{u}}
      {X : AlgebraicGeometry.AlgebraicSpace S}
      (Xᵢ : I → AlgebraicGeometry.AlgebraicSpace S) (f : ∀ i, Xᵢ i ⟶ X)
      (sq : ∀ i j, ChosenPullback (f i) (f j))
      (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
      (D : AlgebraicGeometry.AlgebraicSpace.DescentData.Chosen Xᵢ f sq sq₃)
      (i j : I),
      ((AlgebraicGeometry.AlgebraicSpace.overPseudofunctor S).map
          (sq i j).p₁.op.toLoc).toFunctor.obj (D.obj i) ≅
        ((AlgebraicGeometry.AlgebraicSpace.overPseudofunctor S).map
          (sq i j).p₂.op.toLoc).toFunctor.obj (D.obj j))

/- Remark 74.22.4 (2): these pairwise comparison isomorphisms satisfy the cocycle
equation pr₀₂* φᵢₖ = pr₁₂* φⱼₖ ∘ pr₀₁* φᵢⱼ after pullback to every chosen triple
overlap, in the same shape as quasi-coherent descent. -/
@[stacks 0ADJ] #check
  (AlgebraicGeometry.AlgebraicSpace.DescentData.Chosen.cocycle :
    ∀ {I : Type v} {S : AlgebraicGeometry.Scheme.{u}}
      {X : AlgebraicGeometry.AlgebraicSpace S}
      (Xᵢ : I → AlgebraicGeometry.AlgebraicSpace S) (f : ∀ i, Xᵢ i ⟶ X)
      (sq : ∀ i j, ChosenPullback (f i) (f j))
      (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
      (D : AlgebraicGeometry.AlgebraicSpace.DescentData.Chosen Xᵢ f sq sq₃)
      (i j k : I),
      Pseudofunctor.DescentData'.pullHom'
          (fun a b ↦ (AlgebraicGeometry.AlgebraicSpace.DescentData.Chosen.iso
            Xᵢ f sq sq₃ D a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₂ ≫
        Pseudofunctor.DescentData'.pullHom'
          (fun a b ↦ (AlgebraicGeometry.AlgebraicSpace.DescentData.Chosen.iso
            Xᵢ f sq sq₃ D a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₂ (sq₃ i j k).p₃ =
        Pseudofunctor.DescentData'.pullHom'
          (fun a b ↦ (AlgebraicGeometry.AlgebraicSpace.DescentData.Chosen.iso
            Xᵢ f sq sq₃ D a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₃)
