/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_18_10_FMap

/-!
# Lemma 66.18.10

Canonical bijections between morphisms into small étale pushforward, morphisms out of small
étale inverse image, and `f`-maps of sheaves of sets.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
variable (𝒢 : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
variable (ℱ : Sheaf (smallEtaleTopology X) (Type (u + 1)))

/-- Lemma 66.18.10: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic spaces over
`S`. Let `ℱ` be a sheaf of sets on `X_étale` and let `𝒢` be a sheaf of sets on `Y_étale`. There
are canonical bijections between the set of maps `𝒢 ⟶ f_small,* ℱ`, the set of maps
`f_small^{-1} 𝒢 ⟶ ℱ`, and the set of `f`-maps `φ : 𝒢 ⟶ ℱ`. -/
@[stacks 03G4]
def fMapHomEquiv : (𝒢 ⟶ (sheafPushforwardType f).obj ℱ) ≃ FMap f 𝒢 ℱ where
  toFun := FMap.ofPushforwardHom
  invFun := FMap.toPushforwardHom
  left_inv := FMap.toPushforwardHom_ofPushforwardHom
  right_inv := FMap.ofPushforwardHom_toPushforwardHom

/-- `fMapHomEquiv` sends a morphism `𝒢 ⟶ f_small,* ℱ` to the `f`-map with components
`FMap.ofPushforwardHom_app`. -/
@[simp]
theorem fMapHomEquiv_apply (α : 𝒢 ⟶ (sheafPushforwardType f).obj ℱ) (sq : EtaleSquare f) :
    (fMapHomEquiv f 𝒢 ℱ α).app sq = FMap.ofPushforwardHom_app α sq :=
  rfl

/-- The inverse of `fMapHomEquiv` is `FMap.toPushforwardHom`. -/
@[simp]
theorem fMapHomEquiv_symm_apply (φ : FMap f 𝒢 ℱ) :
    (fMapHomEquiv f 𝒢 ℱ).symm φ = FMap.toPushforwardHom φ :=
  rfl

/-- The adjunction bijection between maps `f_small^{-1} 𝒢 ⟶ ℱ` and maps `𝒢 ⟶ f_small,* ℱ`. -/
def fMapInverseImagePushforwardHomEquiv :
    ((sheafPushforwardType f).leftAdjoint.obj 𝒢 ⟶ ℱ) ≃
      (𝒢 ⟶ (sheafPushforwardType f).obj ℱ) :=
  (Adjunction.ofIsRightAdjoint (sheafPushforwardType f)).homEquiv 𝒢 ℱ

/-- `fMapInverseImagePushforwardHomEquiv` is the hom-equivalence of the small étale
pushforward ⊣ inverse image adjunction. -/
theorem fMapInverseImagePushforwardHomEquiv_eq :
    fMapInverseImagePushforwardHomEquiv f 𝒢 ℱ =
      (Adjunction.ofIsRightAdjoint (sheafPushforwardType f)).homEquiv 𝒢 ℱ :=
  rfl

/-- Maps `f_small^{-1} 𝒢 ⟶ ℱ` are canonically equivalent to `f`-maps `φ : 𝒢 ⟶ ℱ`. -/
def fMapInverseImageHomEquiv :
    ((sheafPushforwardType f).leftAdjoint.obj 𝒢 ⟶ ℱ) ≃ FMap f 𝒢 ℱ :=
  (fMapInverseImagePushforwardHomEquiv f 𝒢 ℱ).trans (fMapHomEquiv f 𝒢 ℱ)

/-- `fMapInverseImageHomEquiv` is the adjunction equivalence composed with `fMapHomEquiv`. -/
theorem fMapInverseImageHomEquiv_eq :
    fMapInverseImageHomEquiv f 𝒢 ℱ =
      (fMapInverseImagePushforwardHomEquiv f 𝒢 ℱ).trans (fMapHomEquiv f 𝒢 ℱ) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace

