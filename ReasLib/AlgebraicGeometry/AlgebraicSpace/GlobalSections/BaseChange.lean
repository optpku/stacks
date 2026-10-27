/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.ToSpec

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

/-- The algebraic space over `S` represented by `S ×_{Spec ℤ} Spec R`. -/
def slicedSpecSpace (S : Scheme.{u}) (R : CommRingCat.{u}) : AlgebraicSpace S :=
  ofOver (specOver S R)

/-- `slicedSpecSpace S R` is the representable algebraic space attached to `specOver S R`. -/
theorem slicedSpecSpace_eq (S : Scheme.{u}) (R : CommRingCat.{u}) :
    slicedSpecSpace S R = ofOver (specOver S R) :=
  rfl

/-- The sliced spectrum of `Γ(X, 𝒪_X)` recovers `specGamma X`. -/
theorem specSpace_globalSectionsRing {S : Scheme.{u}} (X : AlgebraicSpace S) :
    slicedSpecSpace S (globalSectionsRing X) = specGamma X :=
  rfl

/-- `Spec.map φ` is a morphism over `Spec ℤ`. -/
theorem specMap_w {R R' : CommRingCat.{u}} (φ : R ⟶ R') :
    Spec.map φ ≫ specULiftZIsTerminal.from (Spec R) =
      specULiftZIsTerminal.from (Spec R') :=
  specULiftZIsTerminal.hom_ext _ _

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
    slicedSpecSpace S R' ⟶ slicedSpecSpace S R :=
  ofOverMap (specMapOver S φ)

/-- `specMap S φ` is `ofOverMap` of `specMapOver S φ`. -/
theorem specMap_eq (S : Scheme.{u}) {R R' : CommRingCat.{u}} (φ : R ⟶ R') :
    specMap S φ = ofOverMap (specMapOver S φ) :=
  rfl

/-- A morphism of affine schemes, viewed as a morphism of algebraic spaces over `S`,
is affine. -/
instance affine_specMap (S : Scheme.{u}) {R R' : CommRingCat.{u}} (φ : R ⟶ R') :
    Affine (specMap S φ) :=
  sorry

/-- The fibre product `X ×_{Spec Γ(X, 𝒪_X)} Spec A'` of algebraic spaces over `S`. -/
def baseChangeSpec {S : Scheme.{u}} (X : AlgebraicSpace S) {A' : CommRingCat.{u}}
    (φ : globalSectionsRing X ⟶ A') : AlgebraicSpace S :=
  pullback (specMap S φ) (toSpecGamma X)

/-- `baseChangeSpec X φ` is the pullback of `toSpecGamma X` along `specMap S φ`. -/
theorem baseChangeSpec_eq {S : Scheme.{u}} (X : AlgebraicSpace S) {A' : CommRingCat.{u}}
    (φ : globalSectionsRing X ⟶ A') :
    baseChangeSpec X φ = pullback (specMap S φ) (toSpecGamma X) :=
  rfl

/-- The projection `X ×_{Spec Γ(X, 𝒪_X)} Spec A' ⟶ X`. -/
def baseChangeSpecHom {S : Scheme.{u}} (X : AlgebraicSpace S) {A' : CommRingCat.{u}}
    (φ : globalSectionsRing X ⟶ A') : baseChangeSpec X φ ⟶ X :=
  pullback.snd (specMap S φ) (toSpecGamma X)

/-- `baseChangeSpecHom X φ` is the second projection of the defining pullback. -/
theorem baseChangeSpecHom_eq {S : Scheme.{u}} (X : AlgebraicSpace S) {A' : CommRingCat.{u}}
    (φ : globalSectionsRing X ⟶ A') :
    baseChangeSpecHom X φ = pullback.snd (specMap S φ) (toSpecGamma X) :=
  rfl

/-- The projection `X ×_{Spec Γ(X, 𝒪_X)} Spec A' ⟶ Spec A'` over `S`. -/
def baseChangeSpecToSpec {S : Scheme.{u}} (X : AlgebraicSpace S) {A' : CommRingCat.{u}}
    (φ : globalSectionsRing X ⟶ A') : baseChangeSpec X φ ⟶ slicedSpecSpace S A' :=
  pullback.fst (specMap S φ) (toSpecGamma X)

/-- `baseChangeSpecToSpec X φ` is the first projection of the defining pullback. -/
theorem baseChangeSpecToSpec_eq {S : Scheme.{u}} (X : AlgebraicSpace S) {A' : CommRingCat.{u}}
    (φ : globalSectionsRing X ⟶ A') :
    baseChangeSpecToSpec X φ = pullback.fst (specMap S φ) (toSpecGamma X) :=
  rfl

/-- The defining square of `baseChangeSpec X φ` is a pullback. -/
theorem isPullback_baseChangeSpec {S : Scheme.{u}} (X : AlgebraicSpace S)
    {A' : CommRingCat.{u}} (φ : globalSectionsRing X ⟶ A') :
    IsPullback (baseChangeSpecToSpec X φ) (baseChangeSpecHom X φ)
      (specMap S φ) (toSpecGamma X) :=
  IsPullback.of_hasPullback (specMap S φ) (toSpecGamma X)

/-- The projection to the original space from its spectrum base change is affine. -/
instance affine_baseChangeSpecHom {S : Scheme.{u}} (X : AlgebraicSpace S)
    {A' : CommRingCat.{u}} (φ : globalSectionsRing X ⟶ A') :
    Affine (baseChangeSpecHom X φ) :=
  affine_pullback_snd (specMap S φ) (toSpecGamma X)

/-- The scheme projection from the sliced spectrum over `S` to `Spec R`. -/
def specSpace_fst (S : Scheme.{u}) (R : CommRingCat.{u}) :
    (specOver S R).left ⟶ Spec R :=
  pullback.fst (overSpecZ (Spec R)).hom (specULiftZIsTerminal.from S)

namespace GlobalSections

/-- The scheme map to `Spec R` obtained by restricting a morphism into the sliced
spectrum to the chosen atlas and projecting to `Spec R`. -/
def specSpaceAtlasMap {S : Scheme.{u}} {Y : AlgebraicSpace S} {R : CommRingCat.{u}}
    (f : Y ⟶ slicedSpecSpace S R) : (chosenPresentation Y).U.left ⟶ Spec R :=
  (Yoneda.fullyFaithful.preimage
    ((chosenPresentation Y).atlas ≫ f :
      yoneda.obj (chosenPresentation Y).U ⟶ yoneda.obj (specOver S R))).left ≫
    specSpace_fst S R

/-- Pullback of functions from `Spec R` to the chosen atlas agrees along the two
relation projections of the presentation. -/
theorem specSpaceGlobalSectionsMap_equalizes {S : Scheme.{u}} {Y : AlgebraicSpace S}
    {R : CommRingCat.{u}} (f : Y ⟶ slicedSpecSpace S R) :
    ((Scheme.ΓSpecIso R).inv ≫ (specSpaceAtlasMap f).appTop) ≫
        (chosenPresentation Y).tAppTop =
      ((Scheme.ΓSpecIso R).inv ≫ (specSpaceAtlasMap f).appTop) ≫
        (chosenPresentation Y).sAppTop :=
  sorry

/-- The canonical ring map on global sections induced by a morphism to the sliced
spectrum, using its projection to `Spec R`. -/
def specSpaceGlobalSectionsMap {S : Scheme.{u}} {Y : AlgebraicSpace S}
    {R : CommRingCat.{u}} (f : Y ⟶ slicedSpecSpace S R) : R ⟶ globalSectionsRing Y :=
  equalizer.lift ((Scheme.ΓSpecIso R).inv ≫ (specSpaceAtlasMap f).appTop)
    (specSpaceGlobalSectionsMap_equalizes f)

/-- The canonical map on global sections restricts to pullback of functions on the
chosen atlas. -/
theorem specSpaceGlobalSectionsMap_comp_ι {S : Scheme.{u}} {Y : AlgebraicSpace S}
    {R : CommRingCat.{u}} (f : Y ⟶ slicedSpecSpace S R) :
    specSpaceGlobalSectionsMap f ≫ globalSectionsRing_ι Y =
      (Scheme.ΓSpecIso R).inv ≫ (specSpaceAtlasMap f).appTop :=
  equalizer.lift_ι _ _

end GlobalSections

/-- The canonical map from the base-change ring to global sections of the spectrum
base change, induced by its projection to the sliced spectrum. -/
def baseChangeSpecGlobalSectionsMap {S : Scheme.{u}} (X : AlgebraicSpace S)
    {A' : CommRingCat.{u}} (φ : globalSectionsRing X ⟶ A') :
    A' ⟶ globalSectionsRing (baseChangeSpec X φ) :=
  GlobalSections.specSpaceGlobalSectionsMap (baseChangeSpecToSpec X φ)

end AlgebraicGeometry.AlgebraicSpace
