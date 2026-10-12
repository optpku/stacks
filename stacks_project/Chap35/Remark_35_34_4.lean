/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.DescentData
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits

universe u v

/- Remark 35.34.4 (1): the pairwise comparison maps of scheme descent data are
isomorphisms between the pullbacks to the chosen pairwise overlaps. -/
@[stacks 02VQ] #check
  (AlgebraicGeometry.Scheme.DescentData.Chosen.iso :
    ∀ {I : Type v} {S : AlgebraicGeometry.Scheme.{u}}
      (X : I → AlgebraicGeometry.Scheme.{u}) (f : ∀ i, X i ⟶ S)
      (sq : ∀ i j, ChosenPullback (f i) (f j))
      (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
      (D : AlgebraicGeometry.Scheme.DescentData.Chosen X f sq sq₃) (i j : I),
      (AlgebraicGeometry.Scheme.overPseudofunctor.map (sq i j).p₁.op.toLoc).toFunctor.obj
          (D.obj i) ≅
        (AlgebraicGeometry.Scheme.overPseudofunctor.map
          (sq i j).p₂.op.toLoc).toFunctor.obj (D.obj j))

/- Remark 35.34.4 (2): these pairwise comparison isomorphisms satisfy the cocycle
equation after pullback to every chosen triple overlap. -/
@[stacks 02VQ] #check
  (AlgebraicGeometry.Scheme.DescentData.Chosen.cocycle :
    ∀ {I : Type v} {S : AlgebraicGeometry.Scheme.{u}}
      (X : I → AlgebraicGeometry.Scheme.{u}) (f : ∀ i, X i ⟶ S)
      (sq : ∀ i j, ChosenPullback (f i) (f j))
      (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
      (D : AlgebraicGeometry.Scheme.DescentData.Chosen X f sq sq₃) (i j k : I),
      Pseudofunctor.DescentData'.pullHom'
          (fun a b ↦ (AlgebraicGeometry.Scheme.DescentData.Chosen.iso
            X f sq sq₃ D a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₂ ≫
        Pseudofunctor.DescentData'.pullHom'
          (fun a b ↦ (AlgebraicGeometry.Scheme.DescentData.Chosen.iso
            X f sq sq₃ D a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₂ (sq₃ i j k).p₃ =
        Pseudofunctor.DescentData'.pullHom'
          (fun a b ↦ (AlgebraicGeometry.Scheme.DescentData.Chosen.iso
            X f sq sq₃ D a b).hom)
          (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₃)
