/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Big
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.IdentityRelocalization

/-! # Ringed relocalization from spaces-étale to big étale sites -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale
open RingedSite.ToposHom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Inverse image of ring sheaves along `i_f`, i.e. restriction along relocalization. -/
abbrev relocalizationPushforward (f : Y ⟶ X) :
    Sheaf (overEtaleTopology X) RingCat.{u} ⥤ Sheaf (spacesEtaleTopology Y) RingCat.{u} :=
  (relocalizationFunctor f).sheafPushforwardContinuous RingCat.{u}
    (spacesEtaleTopology Y) (overEtaleTopology X)

/-- Inverse image along `i_f` evaluates to global sections of the relocalized object. -/
theorem relocalizationPushforward_obj_obj (f : Y ⟶ X) (U : spacesEtaleSite Y) :
    ((relocalizationPushforward f).obj (Big.structureSheaf X)).obj.obj (op U) =
      Big.gamma ((relocalizationFunctor f).obj U).left :=
  rfl

/-- Type-`u` morphism of topoi `i_f : Sh(Y_spaces,étale) ⟶ Sh((Spaces/X)_étale)`. -/
def relocalizationMorphismOfTopoi (f : Y ⟶ X) :
    MorphismOfTopoiIn.{u + 1, u + 1, u + 1, u + 1, u}
      (overEtaleTopology X) (spacesEtaleTopology Y) where
  inverseImageFunctor :=
    LeftExactFunctor.of
      ((relocalizationFunctor f).sheafPushforwardContinuous (Type u)
        (spacesEtaleTopology Y) (overEtaleTopology X))
  pushforward := directImageTypeU f
  adjunction := inverseImageDirectImageAdjunctionTypeU f

/-- The underlying inverse image of `relocalizationMorphismOfTopoi f` is restriction along
relocalization. -/
theorem relocalizationMorphismOfTopoi_inverseImage (f : Y ⟶ X) :
    (relocalizationMorphismOfTopoi f).inverseImage =
      (relocalizationFunctor f).sheafPushforwardContinuous (Type u)
        (spacesEtaleTopology Y) (overEtaleTopology X) :=
  rfl

/-- Direct-image comparison `𝒪_Y ⟶ i_f⁻¹ 𝒪` on spaces-étale sites, objectwise
`𝒪_Y(U) ⟶ Γ(U, 𝒪_U)`. -/
def relocalizationStructureSheafMap (f : Y ⟶ X) :
    spacesStructureSheaf Y ⟶ (relocalizationPushforward f).obj (Big.structureSheaf X) :=
  InducedCategory.homMk
    { app := fun U => Big.spacesStructureToGamma U.unop
      naturality := fun _ _ _ => sorry }

/-- Component of `relocalizationStructureSheafMap f` at `U/Y`. -/
theorem relocalizationStructureSheafMap_app (f : Y ⟶ X) (U : spacesEtaleSite Y) :
    (relocalizationStructureSheafMap f).hom.app (op U) = Big.spacesStructureToGamma U :=
  rfl

/-- The comparison `𝒪_Y ⟶ i_f⁻¹ 𝒪` is an isomorphism of ring sheaves; its inverse is the
source map `i_f^♯ : i_f⁻¹ 𝒪 ⟶ 𝒪_Y`. -/
instance relocalizationStructureSheafMap_isIso (f : Y ⟶ X) :
    IsIso (relocalizationStructureSheafMap f) :=
  sorry

/-- The underlying inverse-image structure map is the inverse section comparison,
transported through the canonical coefficient-forgetful isomorphisms. -/
def relocalizationSharpUnderlying (f : Y ⟶ X) :
    (sheafCompose (spacesEtaleTopology Y) (forget RingCat.{u})).obj
        ((relocalizationMorphismOfTopoi f).ringInverseImage.obj (Big.structureSheaf X)) ⟶
      (sheafCompose (spacesEtaleTopology Y) (forget RingCat.{u})).obj
        (spacesStructureSheaf Y) :=
  (relocalizationMorphismOfTopoi f).ringInverseImageForgetIso.hom.app
      (Big.structureSheaf X) ≫
    (eqToIso (Functor.sheafPushforwardContinuous.compSheafCompose
      (relocalizationFunctor f) (forget RingCat.{u})
      (spacesEtaleTopology Y) (overEtaleTopology X))).inv.app (Big.structureSheaf X) ≫
    (sheafCompose (spacesEtaleTopology Y) (forget RingCat.{u})).map
      (inv (relocalizationStructureSheafMap f))

/-- Each component of the inverse-image structure map preserves one. -/
theorem relocalizationSharp_map_one (f : Y ⟶ X) (U : (spacesEtaleSite Y)ᵒᵖ) :
    (relocalizationSharpUnderlying f).hom.app U
        (1 : ((relocalizationMorphismOfTopoi f).ringInverseImage.obj
          (Big.structureSheaf X)).obj.obj U) =
      (1 : (spacesStructureSheaf Y).obj.obj U) :=
  sorry

/-- Each component of the inverse-image structure map preserves multiplication. -/
theorem relocalizationSharp_map_mul (f : Y ⟶ X) (U : (spacesEtaleSite Y)ᵒᵖ)
    (a b : ((relocalizationMorphismOfTopoi f).ringInverseImage.obj
      (Big.structureSheaf X)).obj.obj U) :
    (relocalizationSharpUnderlying f).hom.app U (a * b) =
      Mul.mul (α := (spacesStructureSheaf Y).obj.obj U)
        ((relocalizationSharpUnderlying f).hom.app U a)
        ((relocalizationSharpUnderlying f).hom.app U b) :=
  sorry

/-- Each component of the inverse-image structure map preserves zero. -/
theorem relocalizationSharp_map_zero (f : Y ⟶ X) (U : (spacesEtaleSite Y)ᵒᵖ) :
    (relocalizationSharpUnderlying f).hom.app U
        (0 : ((relocalizationMorphismOfTopoi f).ringInverseImage.obj
          (Big.structureSheaf X)).obj.obj U) =
      (0 : (spacesStructureSheaf Y).obj.obj U) :=
  sorry

/-- Each component of the inverse-image structure map preserves addition. -/
theorem relocalizationSharp_map_add (f : Y ⟶ X) (U : (spacesEtaleSite Y)ᵒᵖ)
    (a b : ((relocalizationMorphismOfTopoi f).ringInverseImage.obj
      (Big.structureSheaf X)).obj.obj U) :
    (relocalizationSharpUnderlying f).hom.app U (a + b) =
      Add.add (α := (spacesStructureSheaf Y).obj.obj U)
        ((relocalizationSharpUnderlying f).hom.app U a)
        ((relocalizationSharpUnderlying f).hom.app U b) :=
  sorry

/-- The canonical ring-valued inverse-image structure map of étale relocalization. -/
def relocalizationSharp (f : Y ⟶ X) :
    (relocalizationMorphismOfTopoi f).ringInverseImage.obj (Big.structureSheaf X) ⟶
      spacesStructureSheaf Y :=
  InducedCategory.homMk
    { app := fun U ↦
        let source : RingCat.{u} :=
          ((relocalizationMorphismOfTopoi f).ringInverseImage.obj (Big.structureSheaf X)).obj.obj U
        let target : RingCat.{u} := (spacesStructureSheaf Y).obj.obj U
        @RingCat.ofHom source target source.ring target.ring
        { toFun := (relocalizationSharpUnderlying f).hom.app U
          map_one' := relocalizationSharp_map_one f U
          map_mul' := relocalizationSharp_map_mul f U
          map_zero' := relocalizationSharp_map_zero f U
          map_add' := relocalizationSharp_map_add f U }
      naturality := fun U V h ↦ by
        ext a
        exact ConcreteCategory.congr_hom ((relocalizationSharpUnderlying f).hom.naturality h) a }

/-- Forgetting ring structure recovers the specified inverse section comparison. -/
theorem relocalizationSharp_underlying (f : Y ⟶ X) :
    (sheafCompose (spacesEtaleTopology Y) (forget RingCat.{u})).map
      (relocalizationSharp f) = relocalizationSharpUnderlying f := by
  ext U a
  rfl

/-- The canonical inverse-image structure map of relocalization is invertible. -/
instance relocalizationSharp_isIso (f : Y ⟶ X) : IsIso (relocalizationSharp f) :=
  sorry

/-- Étale relocalization with its canonical inverse-image structure-sheaf map. -/
def relocalizationRingedHom (f : Y ⟶ X) :
    RingedSite.ToposHom (spacesRingedSite Y) (Big.ringedSite X) where
  toTopos := relocalizationMorphismOfTopoi f
  structureMap := relocalizationSharp f

/-- The underlying topos morphism is étale relocalization. -/
theorem relocalizationRingedHom_toTopos (f : Y ⟶ X) :
    (relocalizationRingedHom f).toTopos = relocalizationMorphismOfTopoi f := rfl

/-- The structure map is the canonical inverse-image comparison. -/
theorem relocalizationRingedHom_structureMap (f : Y ⟶ X) :
    (relocalizationRingedHom f).structureMap = relocalizationSharp f := rfl

/-- Identity-base ringed relocalization is relocalization along the identity. -/
def identityRingedRelocalization (X : AlgebraicSpace S) :
    RingedSite.ToposHom (spacesRingedSite X) (Big.ringedSite X) :=
  relocalizationRingedHom (𝟙 X)

/-- Identity-base ringed relocalization specializes the entire ringed morphism. -/
theorem identityRingedRelocalization_eq (X : AlgebraicSpace S) :
    identityRingedRelocalization X = relocalizationRingedHom (𝟙 X) := rfl

/-- Ringed relocalization commutes with big étale postcomposition. -/
def relocalizationRingedHomCompIso {Z : AlgebraicSpace S} (f : Y ⟶ X) (g : Z ⟶ Y) :
    TwoIso.{u + 1, u + 1, u + 1, u + 1, u}
      (comp.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u}
        (relocalizationRingedHom g) (Big.ringedHom f))
      (relocalizationRingedHom (g ≫ f)) where
  homIso :=
    Adjunction.rightAdjointUniq
      (((Big.ringedMorphismOfTopoi f).adjunction.comp
        (relocalizationMorphismOfTopoi g).adjunction).ofNatIsoLeft
        (Functor.sheafPushforwardContinuousComp'
          (Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft (MorphismProperty.Over.forget (@Etale S) ⊤ Z)
              (Over.mapComp g f).symm)
          (Type u) (spacesEtaleTopology Z) (overEtaleTopology Y) (overEtaleTopology X)))
      (relocalizationMorphismOfTopoi (g ≫ f)).adjunction
  comm := by sorry

/-- Identity-base relocalization as a morphism of ringed sites, i.e. `π_X`. -/
def siteHom (X : AlgebraicSpace S) :
    RingedSite.Hom (Big.ringedSite X) (spacesRingedSite X) where
  base := relocalizationFunctor (𝟙 X)
  structureSheafMap := relocalizationStructureSheafMap (𝟙 X)

/-- The base functor of `siteHom X` is identity-base relocalization. -/
theorem siteHom_base (X : AlgebraicSpace S) :
    (siteHom X).base = relocalizationFunctor (𝟙 X) :=
  rfl

/-- Direct-image structure map of `π_X`, i.e. `π_X^♯ : 𝒪_X ⟶ π_{X,*} 𝒪`. -/
def siteSharp (X : AlgebraicSpace S) :
    spacesStructureSheaf X ⟶ (relocalizationPushforward (𝟙 X)).obj (Big.structureSheaf X) :=
  (siteHom X).structureSheafMap

/-- `siteSharp X` is the structure-sheaf map of `siteHom X`. -/
theorem siteSharp_eq (X : AlgebraicSpace S) :
    siteSharp X = (siteHom X).structureSheafMap :=
  rfl

/-- On `U/X`, `π_X^♯` compares `𝒪_X(U)` with `(π_{X,*} 𝒪)(U) = 𝒪(U)`. -/
theorem siteSharp_app (X : AlgebraicSpace S) (U : spacesEtaleSite X) :
    (siteSharp X).hom.app (op U) = Big.spacesStructureToGamma U :=
  rfl

/-- `i_X` is the special case of `i_f` with `f = 𝟙 X`. -/
def identityRelocalization (X : AlgebraicSpace S) :
    MorphismOfTopoiIn.{u + 1, u + 1, u + 1, u + 1, u}
      (overEtaleTopology X) (spacesEtaleTopology X) :=
  relocalizationMorphismOfTopoi (𝟙 X)

/-- `identityRelocalization X` is `relocalizationMorphismOfTopoi` along `𝟙 X`. -/
theorem identityRelocalization_eq (X : AlgebraicSpace S) :
    identityRelocalization X = relocalizationMorphismOfTopoi (𝟙 X) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig

