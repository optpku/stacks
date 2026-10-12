/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import stacks_project.Chap74.Definition_74_22_3_DescentData
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits

universe u

variable {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
variable (f : Y ⟶ X)
variable (sq : ChosenPullback f f) (sq₃ : ChosenPullback₃ sq sq sq)
variable (D : AlgebraicGeometry.AlgebraicSpace.DescentData.Chosen
  (fun _ : PUnit ↦ Y) (fun _ ↦ f) (fun _ _ ↦ sq) (fun _ _ _ ↦ sq₃))

/- Remark 74.22.2 (1): for a descent datum `(V / Y, φ)` relative to `Y ⟶ X`, the comparison
`φ` is an isomorphism `pr₀* V ≅ pr₁* V` of algebraic spaces over the chosen overlap
`Y ×_X Y`. Here `sq.p₁` and `sq.p₂` are `pr₀` and `pr₁`, and
`(overPseudofunctor S).map` is the slice pullback
`(Y ×_X Y) ×_{prᵢ, Y} V`. -/
@[stacks 0ADH] #check
  (AlgebraicGeometry.AlgebraicSpace.DescentData.Chosen.iso
      (fun _ : PUnit ↦ Y) (fun _ ↦ f) (fun _ _ ↦ sq) (fun _ _ _ ↦ sq₃)
      D PUnit.unit PUnit.unit :
    ((AlgebraicGeometry.AlgebraicSpace.overPseudofunctor S).map
          sq.p₁.op.toLoc).toFunctor.obj (D.obj PUnit.unit) ≅
      ((AlgebraicGeometry.AlgebraicSpace.overPseudofunctor S).map
          sq.p₂.op.toLoc).toFunctor.obj (D.obj PUnit.unit))

/- Remark 74.22.2 (2): the cocycle then reads `pr₀₂* φ = pr₁₂* φ ∘ pr₀₁* φ` after pullback
to a chosen triple overlap, in the same shape as quasi-coherent descent.
`pullHom'` along `sq₃.p` with `(p₁, p₂)`, `(p₂, p₃)`, `(p₁, p₃)` is `pr₀₁*`, `pr₁₂*`,
`pr₀₂*`; Lean `≫` is Stacks `∘` in reverse order. -/
@[stacks 0ADH] #check
  (AlgebraicGeometry.AlgebraicSpace.DescentData.Chosen.cocycle
      (fun _ : PUnit ↦ Y) (fun _ ↦ f) (fun _ _ ↦ sq) (fun _ _ _ ↦ sq₃)
      D PUnit.unit PUnit.unit PUnit.unit :
    CategoryTheory.Pseudofunctor.DescentData'.pullHom'
          (fun a b ↦ (AlgebraicGeometry.AlgebraicSpace.DescentData.Chosen.iso
            (fun _ : PUnit ↦ Y) (fun _ ↦ f) (fun _ _ ↦ sq) (fun _ _ _ ↦ sq₃)
            D a b).hom)
          sq₃.p sq₃.p₁ sq₃.p₂ ≫
        CategoryTheory.Pseudofunctor.DescentData'.pullHom'
          (fun a b ↦ (AlgebraicGeometry.AlgebraicSpace.DescentData.Chosen.iso
            (fun _ : PUnit ↦ Y) (fun _ ↦ f) (fun _ _ ↦ sq) (fun _ _ _ ↦ sq₃)
            D a b).hom)
          sq₃.p sq₃.p₂ sq₃.p₃ =
      CategoryTheory.Pseudofunctor.DescentData'.pullHom'
        (fun a b ↦ (AlgebraicGeometry.AlgebraicSpace.DescentData.Chosen.iso
          (fun _ : PUnit ↦ Y) (fun _ ↦ f) (fun _ _ ↦ sq) (fun _ _ _ ↦ sq₃)
          D a b).hom)
        sq₃.p sq₃.p₁ sq₃.p₃)
