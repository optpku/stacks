module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap67.Lemma_67_20_5_Pullback
public import stacks_project.Chap69.Lemma_69_16_2_ToSpec

/-!
# Spec-fibre products of algebraic spaces

An algebraic space `X` over `S` may be base-changed along a ring map
`Γ(X, 𝒪_X) ⟶ A'` by forming the fibre product of `toSpecGamma` with the
sliced morphism `Spec A' ⟶ Spec Γ(X, 𝒪_X)` over `S`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The scheme over `S` obtained by pulling `Spec R` back along the unique morphism
`S ⟶ Spec ℤ`. -/
def specOver (S : Scheme.{u}) (R : CommRingCat.{u}) : Over S :=
  (Over.pullback (specULiftZIsTerminal.from S)).obj (overSpecZ (Spec R))

/-- `specOver S R` is the pullback of `overSpecZ (Spec R)` along `S ⟶ Spec ℤ`. -/
theorem specOver_eq (S : Scheme.{u}) (R : CommRingCat.{u}) :
    specOver S R =
      (Over.pullback (specULiftZIsTerminal.from S)).obj (overSpecZ (Spec R)) :=
  rfl

/-- The algebraic space over `S` representing maps to `Spec R`. -/
def specSpace (S : Scheme.{u}) (R : CommRingCat.{u}) : AlgebraicSpace S :=
  ofOver (specOver S R)

/-- `specSpace S R` is the representable algebraic space attached to `specOver S R`. -/
theorem specSpace_eq (S : Scheme.{u}) (R : CommRingCat.{u}) :
    specSpace S R = ofOver (specOver S R) :=
  rfl

/-- The sliced spectrum of `Γ(X, 𝒪_X)` recovers `specGamma X`. -/
theorem specSpace_globalSectionsRing {S : Scheme.{u}} (X : AlgebraicSpace S) :
    specSpace S (globalSectionsRing X) = specGamma X :=
  rfl

/-- `Spec.map φ` is a morphism over `Spec ℤ`. -/
theorem specMap_w {R R' : CommRingCat.{u}} (φ : R ⟶ R') :
    Spec.map φ ≫ specULiftZIsTerminal.from (Spec R) =
      specULiftZIsTerminal.from (Spec R') :=
  sorry

/-- The morphism `Spec R' ⟶ Spec R` over `S`, as the base change of `Spec.map φ`
along `S ⟶ Spec ℤ`. -/
def specMapOver (S : Scheme.{u}) {R R' : CommRingCat.{u}} (φ : R ⟶ R') :
    specOver S R' ⟶ specOver S R :=
  (Over.pullback (specULiftZIsTerminal.from S)).map (Over.homMk (Spec.map φ) (specMap_w φ))

/-- `specMapOver S φ` is `Over.pullback.map` of `Over.homMk` of `Spec.map φ`. -/
theorem specMapOver_eq (S : Scheme.{u}) {R R' : CommRingCat.{u}} (φ : R ⟶ R') :
    specMapOver S φ =
      (Over.pullback (specULiftZIsTerminal.from S)).map
        (Over.homMk (Spec.map φ) (specMap_w φ)) :=
  rfl

/-- The morphism of algebraic spaces over `S` induced by a ring map `R ⟶ R'`. -/
def specMap (S : Scheme.{u}) {R R' : CommRingCat.{u}} (φ : R ⟶ R') :
    specSpace S R' ⟶ specSpace S R :=
  ofOverMap (specMapOver S φ)

/-- `specMap S φ` is `ofOverMap` of `specMapOver S φ`. -/
theorem specMap_eq (S : Scheme.{u}) {R R' : CommRingCat.{u}} (φ : R ⟶ R') :
    specMap S φ = ofOverMap (specMapOver S φ) :=
  rfl

/-- The morphism `Spec A' ⟶ Spec Γ(X, 𝒪_X)` of algebraic spaces over `S`. -/
abbrev specMapToGamma {S : Scheme.{u}} (X : AlgebraicSpace S) {A' : CommRingCat.{u}}
    (φ : globalSectionsRing X ⟶ A') : specSpace S A' ⟶ specGamma X :=
  specMap S φ

/-- `specMapToGamma X φ` is `specMap S φ` into `specGamma X`. -/
theorem specMapToGamma_eq {S : Scheme.{u}} (X : AlgebraicSpace S) {A' : CommRingCat.{u}}
    (φ : globalSectionsRing X ⟶ A') : specMapToGamma X φ = specMap S φ :=
  rfl

/-- A morphism of affine schemes, viewed as a morphism of algebraic spaces over `S`,
is affine. -/
instance affine_specMap (S : Scheme.{u}) {R R' : CommRingCat.{u}} (φ : R ⟶ R') :
    Affine (specMap S φ) :=
  sorry

/-- The sliced morphism `Spec A' ⟶ Spec Γ(X, 𝒪_X)` is affine. -/
instance affine_specMapToGamma {S : Scheme.{u}} (X : AlgebraicSpace S)
    {A' : CommRingCat.{u}} (φ : globalSectionsRing X ⟶ A') :
    Affine (specMapToGamma X φ) :=
  affine_specMap S φ

/-- The fibre product `X ×_{Spec Γ(X, 𝒪_X)} Spec A'` of algebraic spaces over `S`. -/
def baseChangeSpec {S : Scheme.{u}} (X : AlgebraicSpace S) {A' : CommRingCat.{u}}
    (φ : globalSectionsRing X ⟶ A') : AlgebraicSpace S :=
  pullback (specMapToGamma X φ) (toSpecGamma X)

/-- `baseChangeSpec X φ` is the pullback of `toSpecGamma X` along `specMapToGamma X φ`. -/
theorem baseChangeSpec_eq {S : Scheme.{u}} (X : AlgebraicSpace S) {A' : CommRingCat.{u}}
    (φ : globalSectionsRing X ⟶ A') :
    baseChangeSpec X φ = pullback (specMapToGamma X φ) (toSpecGamma X) :=
  rfl

/-- The projection `X ×_{Spec Γ(X, 𝒪_X)} Spec A' ⟶ X`. -/
def baseChangeSpecHom {S : Scheme.{u}} (X : AlgebraicSpace S) {A' : CommRingCat.{u}}
    (φ : globalSectionsRing X ⟶ A') : baseChangeSpec X φ ⟶ X :=
  pullback.snd (specMapToGamma X φ) (toSpecGamma X)

/-- `baseChangeSpecHom X φ` is the second projection of the defining pullback. -/
theorem baseChangeSpecHom_eq {S : Scheme.{u}} (X : AlgebraicSpace S) {A' : CommRingCat.{u}}
    (φ : globalSectionsRing X ⟶ A') :
    baseChangeSpecHom X φ = pullback.snd (specMapToGamma X φ) (toSpecGamma X) :=
  rfl

/-- The projection `X ×_{Spec Γ(X, 𝒪_X)} Spec A' ⟶ Spec A'` over `S`. -/
def baseChangeSpecToSpec {S : Scheme.{u}} (X : AlgebraicSpace S) {A' : CommRingCat.{u}}
    (φ : globalSectionsRing X ⟶ A') : baseChangeSpec X φ ⟶ specSpace S A' :=
  pullback.fst (specMapToGamma X φ) (toSpecGamma X)

/-- `baseChangeSpecToSpec X φ` is the first projection of the defining pullback. -/
theorem baseChangeSpecToSpec_eq {S : Scheme.{u}} (X : AlgebraicSpace S) {A' : CommRingCat.{u}}
    (φ : globalSectionsRing X ⟶ A') :
    baseChangeSpecToSpec X φ = pullback.fst (specMapToGamma X φ) (toSpecGamma X) :=
  rfl

/-- The defining square of `baseChangeSpec X φ` is a pullback. -/
theorem isPullback_baseChangeSpec {S : Scheme.{u}} (X : AlgebraicSpace S)
    {A' : CommRingCat.{u}} (φ : globalSectionsRing X ⟶ A') :
    IsPullback (baseChangeSpecToSpec X φ) (baseChangeSpecHom X φ)
      (specMapToGamma X φ) (toSpecGamma X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
