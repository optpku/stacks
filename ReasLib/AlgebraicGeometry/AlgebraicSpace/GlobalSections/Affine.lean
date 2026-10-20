/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Presentation.Descent
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Global sections and morphisms to affine schemes

The structure morphism to an affine scheme induces a ring map into the presentation
equalizer defining global sections, with its comparison to the chosen atlas.
Morphisms from an algebraic space over `Spec ℤ` to an affine scheme are classified
by ring maps on global sections.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

variable {A : Type u} [CommRing A]
variable {X : AlgebraicSpace (Spec (CommRingCat.of A))}

/-- The two presentation restrictions agree on the global-sections map of the atlas
structure morphism over `Spec A`. -/
theorem globalSectionsMap_equalizes
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) :
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
          (chosenPresentation X).U.hom.appTop) ≫
        (chosenPresentation X).tAppTop =
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
          (chosenPresentation X).U.hom.appTop) ≫
        (chosenPresentation X).sAppTop :=
  sorry

/-- The structure morphism of an algebraic space over `Spec A` induces the ring map
`A →+* Γ(X, 𝒪_X)`. -/
noncomputable def globalSectionsMap
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) :
    A →+* globalSectionsRing X :=
  (equalizer.lift
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (chosenPresentation X).U.hom.appTop)
      (globalSectionsMap_equalizes f)).hom

/-- After comparison with the chosen atlas, `globalSectionsMap f` recovers the scheme-level
global-sections map of the atlas structure morphism. -/
theorem globalSectionsMap_comp_ι
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) :
    (globalSectionsRing_ι X).hom.comp (globalSectionsMap f) =
      Scheme.Hom.globalSectionsMap (chosenPresentation X).U.hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom


namespace AlgebraicGeometry.AlgebraicSpace

/-- The terminal scheme `Spec ℤ` in universe `u`. -/
abbrev specZ : Scheme.{u} :=
  Spec (.of (ULift.{u} ℤ))

/-- `specZ` is the spectrum of `ULift ℤ`. -/
theorem specZ_eq : specZ.{u} = Spec (.of (ULift.{u} ℤ)) :=
  rfl

/-- A scheme as an object of `Sch / Spec ℤ`. -/
abbrev overSpecZ (T : Scheme.{u}) : Over specZ :=
  Over.mk (specULiftZIsTerminal.from T)

/-- The underlying scheme of `overSpecZ T` is `T`. -/
theorem overSpecZ_left (T : Scheme.{u}) : (overSpecZ T).left = T :=
  rfl

/-- The structure morphism of `overSpecZ T` is the unique map `T ⟶ Spec ℤ`. -/
theorem overSpecZ_hom (T : Scheme.{u}) :
    (overSpecZ T).hom = specULiftZIsTerminal.from T :=
  rfl

namespace GlobalSections

/-- The morphism `U ⟶ T` in `Sch / Spec ℤ` obtained by restricting an algebraic-space morphism
along the chosen atlas. -/
def atlasOverHom {X : AlgebraicSpace specZ} {T : Scheme.{u}}
    (f : X ⟶ ofOver (overSpecZ T)) :
    (chosenPresentation X).U ⟶ overSpecZ T :=
  Yoneda.fullyFaithful.preimage
    ((chosenPresentation X).atlas ≫ f :
      yoneda.obj (chosenPresentation X).U ⟶ yoneda.obj (overSpecZ T))

/-- `atlasOverHom f` is the Yoneda preimage of the atlas composite. -/
theorem atlasOverHom_map {X : AlgebraicSpace specZ} {T : Scheme.{u}}
    (f : X ⟶ ofOver (overSpecZ T)) :
    yoneda.map (atlasOverHom f) =
      ((chosenPresentation X).atlas ≫ f :
        yoneda.obj (chosenPresentation X).U ⟶ yoneda.obj (overSpecZ T)) :=
  sorry

/-- The two presentation restrictions agree on the global-sections map of `atlasOverHom f`. -/
theorem globalSectionsMap_equalizes {X : AlgebraicSpace specZ} {T : Scheme.{u}}
    (f : X ⟶ ofOver (overSpecZ T)) :
    (atlasOverHom f).left.appTop ≫ (chosenPresentation X).tAppTop =
      (atlasOverHom f).left.appTop ≫ (chosenPresentation X).sAppTop :=
  sorry

/-- The map on global sections `f ↦ f^♯` associated to a morphism from an algebraic space to a
scheme. -/
def globalSectionsMap {X : AlgebraicSpace specZ} {T : Scheme.{u}}
    (f : X ⟶ ofOver (overSpecZ T)) : Γ(T, ⊤) ⟶ globalSectionsRing X :=
  equalizer.lift (atlasOverHom f).left.appTop (globalSectionsMap_equalizes f)

/-- `globalSectionsMap f` is the unique lift of `(atlasOverHom f).left.appTop` through the
equalizer inclusion `Γ(X, 𝒪_X) ⟶ Γ(U, 𝒪_U)`. -/
theorem globalSectionsMap_eq_appTop {X : AlgebraicSpace specZ} {T : Scheme.{u}}
    (f : X ⟶ ofOver (overSpecZ T)) :
    globalSectionsMap f ≫ globalSectionsRing_ι X = (atlasOverHom f).left.appTop :=
  sorry

/-- The morphism of schemes `U ⟶ T` classified by a ring map `Γ(T, ⊤) ⟶ Γ(X, 𝒪_X)`. -/
def schemeHomMk {X : AlgebraicSpace specZ} {T : Scheme.{u}} [IsAffine T]
    (φ : Γ(T, ⊤) ⟶ globalSectionsRing X) :
    (chosenPresentation X).U.left ⟶ (overSpecZ T).left :=
  (chosenPresentation X).U.left.toSpecΓ ≫
    Spec.map (φ ≫ globalSectionsRing_ι X) ≫
      (T.isoSpec.inv : Spec Γ(T, ⊤) ⟶ (overSpecZ T).left)

/-- `schemeHomMk φ` is a morphism over `Spec ℤ`. -/
theorem schemeHomMk_w {X : AlgebraicSpace specZ} {T : Scheme.{u}} [IsAffine T]
    (φ : Γ(T, ⊤) ⟶ globalSectionsRing X) :
    schemeHomMk φ ≫ (overSpecZ T).hom = (chosenPresentation X).U.hom :=
  sorry

/-- The morphism in `Sch / Spec ℤ` classified by a ring map `Γ(T, ⊤) ⟶ Γ(X, 𝒪_X)`. -/
def overHomMk {X : AlgebraicSpace specZ} {T : Scheme.{u}} [IsAffine T]
    (φ : Γ(T, ⊤) ⟶ globalSectionsRing X) :
    (chosenPresentation X).U ⟶ overSpecZ T :=
  Over.homMk (schemeHomMk φ) (schemeHomMk_w φ)

/-- The underlying scheme morphism of `overHomMk φ` is `schemeHomMk φ`. -/
theorem overHomMk_left {X : AlgebraicSpace specZ} {T : Scheme.{u}} [IsAffine T]
    (φ : Γ(T, ⊤) ⟶ globalSectionsRing X) :
    (overHomMk φ).left = schemeHomMk φ :=
  sorry

/-- The two relation projections become equal after composing with `ofOverMap (overHomMk φ)`. -/
theorem homMk_equalizes {X : AlgebraicSpace specZ} {T : Scheme.{u}} [IsAffine T]
    (φ : Γ(T, ⊤) ⟶ globalSectionsRing X) :
    ofOverMap (chosenPresentation X).R.t ≫ ofOverMap (overHomMk φ) =
      ofOverMap (chosenPresentation X).R.s ≫ ofOverMap (overHomMk φ) :=
  sorry

/-- The morphism of algebraic spaces `X ⟶ T` classified by a ring map on global sections. -/
def homMk {X : AlgebraicSpace specZ} {T : Scheme.{u}} [IsAffine T]
    (φ : Γ(T, ⊤) ⟶ globalSectionsRing X) : X ⟶ ofOver (overSpecZ T) :=
  Presentation.homDesc (chosenPresentation X) (ofOverMap (overHomMk φ)) (homMk_equalizes φ)

/-- Reconstructing a morphism from its pullback on global sections recovers the morphism. -/
theorem homMk_globalSectionsMap {X : AlgebraicSpace specZ} {T : Scheme.{u}} [IsAffine T]
    (f : X ⟶ ofOver (overSpecZ T)) : homMk (globalSectionsMap f) = f :=
  sorry

/-- Pullback on global sections of the reconstructed morphism recovers the ring map. -/
theorem globalSectionsMap_homMk {X : AlgebraicSpace specZ} {T : Scheme.{u}} [IsAffine T]
    (φ : Γ(T, ⊤) ⟶ globalSectionsRing X) : globalSectionsMap (homMk φ) = φ :=
  sorry

/-- Morphisms from an algebraic space over `Spec ℤ` to an affine scheme `T` are equivalent to
ring maps `Γ(T, ⊤) ⟶ Γ(X, 𝒪_X)`, sending `f` to `f^♯` on global sections. -/
def homEquivAffine {X : AlgebraicSpace specZ} {T : Scheme.{u}} [IsAffine T] :
    (X ⟶ ofOver (overSpecZ T)) ≃ (Γ(T, ⊤) ⟶ globalSectionsRing X) where
  toFun := globalSectionsMap
  invFun := homMk
  left_inv := homMk_globalSectionsMap
  right_inv := globalSectionsMap_homMk

/-- `homEquivAffine` sends a morphism to its map on global sections. -/
theorem homEquivAffine_apply {X : AlgebraicSpace specZ} {T : Scheme.{u}} [IsAffine T]
    (f : X ⟶ ofOver (overSpecZ T)) :
    homEquivAffine f = globalSectionsMap f :=
  rfl

/-- The inverse of `homEquivAffine` is `homMk`. -/
theorem homEquivAffine_symm_apply {X : AlgebraicSpace specZ} {T : Scheme.{u}} [IsAffine T]
    (φ : Γ(T, ⊤) ⟶ globalSectionsRing X) :
    homEquivAffine.symm φ = homMk φ :=
  rfl

end GlobalSections

end AlgebraicGeometry.AlgebraicSpace
