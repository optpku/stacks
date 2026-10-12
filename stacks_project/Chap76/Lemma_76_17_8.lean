/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_17_8_Etale
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom.Deformation

noncomputable section

universe u

/- Lemma 76.17.8: Let `S` be a scheme. Consider a commutative diagram of first-order
thickenings `(T₂ ⊂ T₂') ⟶ (X₂ ⊂ X₂')` over `(T₁ ⊂ T₁') ⟶ (X₁ ⊂ X₁')` and a
commutative diagram `X₂' ⟶ B₂`, `X₁' ⟶ B₁` of algebraic spaces over `S`, with
`X₂ ⟶ X₁` and `B₂ ⟶ B₁` étale. For any `𝒪_{T₁}`-linear map
`θ₁ : a₁^* Ω_{X₁/B₁} ⟶ C_{T₁/T₁'}`, let `θ₂` be the composite of the canonical
étale identification `a₂^* Ω_{X₂/B₂} ≅ h^* a₁^* Ω_{X₁/B₁}`, the pullback `h^* θ₁`,
and the conormal map of the `T`-square. Then the diagram of Remark 76.17.3 actions
`(θ₂ · a₂')` and `(θ₁ · a₁')` commutes. -/
@[stacks 0CK8] #check perturbation_commSq_of_etale
