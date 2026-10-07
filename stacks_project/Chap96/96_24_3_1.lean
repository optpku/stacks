module

public import stacks_project.Chap96.«96_24_3_1_StructureSheaf»
public import stacks_project.Chap96.«96_24_3_1_Comparison»

/-!
# 96.24.3.1

Restriction of `𝒪_𝒳` to `𝒳_affine` is a sheaf `𝒪` for every standard
topology `τ`, and the special cocontinuous inclusion of Lemma 96.24.3
extends to an equivalence of ringed topoi
`(Sh(𝒳_affine,τ), 𝒪) ⟶ (Sh(𝒳_τ), 𝒪_𝒳)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} (X : GroupoidsOver S) (τ : StandardTopology)
variable [HasSheafify (X.associatedAffineTopology τ) (Type (u + 1))]
variable [∀ P : (Affine X)ᵒᵖ ⥤ Type (u + 1),
    (affineInclusion X).op.HasPointwiseRightKanExtension P]
variable [(X.associatedAffineTopology τ).HasSheafCompose (forget RingCat.{u + 1})]
variable [(X.associatedTopology τ).HasSheafCompose (forget RingCat.{u + 1})]

/-- 96.24.3.1: the special cocontinuous inclusion of the associated affine
`τ`-site extends to an equivalence of ringed topoi
`(Sh(𝒳_affine,τ), 𝒪) ⟶ (Sh(𝒳_τ), 𝒪_𝒳)`, where `𝒪` is the restriction of
`𝒪_𝒳`. -/
@[stacks 0H0C]
instance associatedAffineComparison_isEquivalence :
    (associatedAffineComparison X τ).IsEquivalence :=
  sorry

end AlgebraicGeometry.GroupoidsOver
