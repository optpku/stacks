module

public import Mathlib.AlgebraicGeometry.Limits
public import stacks_project.Chap65.Lemma_65_9_1
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap69.Situation_69_16_1_GlobalSections

/-!
# Morphisms from an algebraic space to an affine scheme

The `Γ ⊣ Spec` classification of morphisms into an affine scheme extends from schemes to
algebraic spaces over `Spec ℤ`: a morphism `X ⟶ T` is equivalent to a ring map
`Γ(T, ⊤) ⟶ Γ(X, 𝒪_X)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

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

namespace Presentation

/-- The sheaf morphism associated to `g : ofOver P.U ⟶ Y` equalizes the sheafified kernel-pair
projections of the atlas. -/
theorem homDesc_sheaf_equalizes {S : Scheme.{u}} {X : AlgebraicSpace S}
    (P : Presentation X) {Y : AlgebraicSpace S} (g : ofOver P.U ⟶ Y)
    (h : ofOverMap P.R.t ≫ g = ofOverMap P.R.s ≫ g) :
    (Scheme.fppfTopology.over S).yoneda.map
        (kernelPair P.atlas P.atlas_etale.rep).t ≫
      sheafHom (g : yoneda.obj P.U ⟶ Y.functorOfPoints) =
      (Scheme.fppfTopology.over S).yoneda.map
        (kernelPair P.atlas P.atlas_etale.rep).s ≫
      sheafHom (g : yoneda.obj P.U ⟶ Y.functorOfPoints) :=
  sorry

/-- Descend a morphism out of the presenting scheme along the atlas coequalizer in fppf sheaves. -/
def homDesc {S : Scheme.{u}} {X : AlgebraicSpace S} (P : Presentation X)
    {Y : AlgebraicSpace S} (g : ofOver P.U ⟶ Y)
    (h : ofOverMap P.R.t ≫ g = ofOverMap P.R.s ≫ g) : X ⟶ Y :=
  Sheaf.homEquiv
    (Cofork.IsColimit.desc
      (Classical.choice (isCoequalizer P.atlas P.atlas_etale P.atlas_locallySurjective))
      (sheafHom (g : yoneda.obj P.U ⟶ Y.functorOfPoints))
      (homDesc_sheaf_equalizes P g h))

/-- Precomposing `homDesc` with the atlas recovers the original morphism from the presenting
scheme. -/
theorem homDesc_comp_atlas {S : Scheme.{u}} {X : AlgebraicSpace S} (P : Presentation X)
    {Y : AlgebraicSpace S} (g : ofOver P.U ⟶ Y)
    (h : ofOverMap P.R.t ≫ g = ofOverMap P.R.s ≫ g) :
    P.atlas ≫ homDesc P g h = (g : yoneda.obj P.U ⟶ Y.functorOfPoints) :=
  sorry

end Presentation

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

/-- Morphisms from an algebraic space over `Spec ℤ` to an affine scheme `T` are equivalent to
ring maps `Γ(T, ⊤) ⟶ Γ(X, 𝒪_X)`, sending `f` to `f^♯` on global sections. -/
def homEquivAffine {X : AlgebraicSpace specZ} {T : Scheme.{u}} [IsAffine T] :
    (X ⟶ ofOver (overSpecZ T)) ≃ (Γ(T, ⊤) ⟶ globalSectionsRing X) where
  toFun := globalSectionsMap
  invFun := homMk
  left_inv := sorry
  right_inv := sorry

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
