module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.CategoryTheory.Adjunction.Derived.Unbounded
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Definition_66_29_1_RingedSite
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Pullbacks
public import stacks_project.Chap65.Lemma_65_9_1_KernelPair
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap69.Situation_69_16_1_GlobalSections
public import stacks_project.Chap84.«84_5_2_1_Site»
public import stacks_project.Chap84.Lemma_84_5_2_Relocalization

/-!
# Big étale structure sheaf and derived module functors

The sheaf of rings on `(Spaces/X)_étale` is `U ↦ Γ(U, 𝒪_U)`, the global-sections
sheaf, not `π_X⁻¹ 𝒪_X`. Derived module functors are obtained from the corresponding
pushforwards of sheaves of modules along the section-pullback ring maps of
`Over.pullback`, `Over.map`, and relocalization.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

variable {S : Scheme.{u}}

/-- Pullback along a morphism of algebraic spaces is continuous on big étale slices. -/
instance overEtale_pullback_isContinuous {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    (Over.pullback f).IsContinuous (overEtaleTopology X) (overEtaleTopology Y) :=
  sorry

/-- Postcomposition along a morphism of algebraic spaces is continuous on big étale slices. -/
instance overEtale_map_isContinuous {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    (Over.map f).IsContinuous (overEtaleTopology Y) (overEtaleTopology X) :=
  sorry

/-- The functor of points of an algebraic space, as an fppf sheaf on schemes over `S`. -/
def fppfSpaceSheaf (X : AlgebraicSpace S) :
    Sheaf (Scheme.fppfTopology.over S) (Type u) :=
  ⟨X.functorOfPoints, X.isSheaf⟩

/-- `fppfSpaceSheaf X` is the functor of points of `X`, as an fppf sheaf. -/
theorem fppfSpaceSheaf_eq (X : AlgebraicSpace S) :
    fppfSpaceSheaf X = ⟨X.functorOfPoints, X.isSheaf⟩ :=
  rfl

/-- The morphism of fppf sheaves associated to a map from a scheme to an algebraic space. -/
def fppfYonedaHom {X : AlgebraicSpace S} {U : Over S}
    (φ : yoneda.obj U ⟶ X.functorOfPoints) :
    (Scheme.fppfTopology.over S).yoneda.obj U ⟶ fppfSpaceSheaf X :=
  Sheaf.homEquiv.symm φ

/-- `fppfYonedaHom φ` is the sheaf morphism associated to `φ`. -/
theorem fppfYonedaHom_eq {X : AlgebraicSpace S} {U : Over S}
    (φ : yoneda.obj U ⟶ X.functorOfPoints) :
    fppfYonedaHom φ = Sheaf.homEquiv.symm φ :=
  rfl

/-- The two sheafified kernel-pair projections of a presentation equalize the atlas. -/
theorem fppfYonedaHom_equalizes {X : AlgebraicSpace S} (P : Presentation X) :
    (Scheme.fppfTopology.over S).yoneda.map (kernelPair P.atlas P.atlas_etale.rep).t ≫
        fppfYonedaHom P.atlas =
      (Scheme.fppfTopology.over S).yoneda.map (kernelPair P.atlas P.atlas_etale.rep).s ≫
        fppfYonedaHom P.atlas :=
  sorry

/-- The cofork of an étale atlas in fppf sheaves on schemes over `S`. -/
def presentationCofork {X : AlgebraicSpace S} (P : Presentation X) :
    Cofork
      ((Scheme.fppfTopology.over S).yoneda.map (kernelPair P.atlas P.atlas_etale.rep).t)
      ((Scheme.fppfTopology.over S).yoneda.map (kernelPair P.atlas P.atlas_etale.rep).s) :=
  Cofork.ofπ (fppfYonedaHom P.atlas) (fppfYonedaHom_equalizes P)

/-- `presentationCofork P` is the cofork of the sheafified kernel-pair projections. -/
theorem presentationCofork_eq {X : AlgebraicSpace S} (P : Presentation X) :
    presentationCofork P =
      Cofork.ofπ (fppfYonedaHom P.atlas) (fppfYonedaHom_equalizes P) :=
  rfl

/-- An étale-locally surjective atlas is a coequalizer in fppf sheaves. -/
theorem presentationCofork_isColimit {X : AlgebraicSpace S} (P : Presentation X) :
    Nonempty (IsColimit (presentationCofork P)) :=
  sorry

/-- The sheaf morphism associated to `g : ofOver P.U ⟶ Y` equalizes the kernel-pair
projections of the atlas. -/
theorem presentationDesc_equalizes {X Y : AlgebraicSpace S} (P : Presentation X)
    (g : ofOver P.U ⟶ Y)
    (h : ofOverMap P.R.t ≫ g = ofOverMap P.R.s ≫ g) :
    (Scheme.fppfTopology.over S).yoneda.map (kernelPair P.atlas P.atlas_etale.rep).t ≫
        fppfYonedaHom (g : yoneda.obj P.U ⟶ Y.functorOfPoints) =
      (Scheme.fppfTopology.over S).yoneda.map (kernelPair P.atlas P.atlas_etale.rep).s ≫
        fppfYonedaHom (g : yoneda.obj P.U ⟶ Y.functorOfPoints) :=
  sorry

/-- Descend a morphism out of the presenting scheme along the atlas coequalizer. -/
def presentationDesc {X Y : AlgebraicSpace S} (P : Presentation X)
    (g : ofOver P.U ⟶ Y)
    (h : ofOverMap P.R.t ≫ g = ofOverMap P.R.s ≫ g) : X ⟶ Y :=
  Sheaf.homEquiv
    (Cofork.IsColimit.desc (Classical.choice (presentationCofork_isColimit P))
      (fppfYonedaHom (g : yoneda.obj P.U ⟶ Y.functorOfPoints))
      (presentationDesc_equalizes P g h))

/-- `presentationDesc P g h` is the sheaf-hom equivalent of the cofork descent of `g`. -/
theorem presentationDesc_eq {X Y : AlgebraicSpace S} (P : Presentation X)
    (g : ofOver P.U ⟶ Y)
    (h : ofOverMap P.R.t ≫ g = ofOverMap P.R.s ≫ g) :
    presentationDesc P g h =
      Sheaf.homEquiv
        (Cofork.IsColimit.desc (Classical.choice (presentationCofork_isColimit P))
          (fppfYonedaHom (g : yoneda.obj P.U ⟶ Y.functorOfPoints))
          (presentationDesc_equalizes P g h)) :=
  rfl

/-- The scheme over `S` obtained by pulling `Spec Γ(X, 𝒪_X)` back along `S ⟶ Spec ℤ`. -/
def specGammaOver (X : AlgebraicSpace S) : Over S :=
  (Over.pullback (specULiftZIsTerminal.from S)).obj
    (Over.mk (specULiftZIsTerminal.from (Spec (globalSectionsRing X))))

/-- `specGammaOver X` is the pullback of `Spec Γ(X, 𝒪_X)` along `S ⟶ Spec ℤ`. -/
theorem specGammaOver_eq (X : AlgebraicSpace S) :
    specGammaOver X =
      (Over.pullback (specULiftZIsTerminal.from S)).obj
        (Over.mk (specULiftZIsTerminal.from (Spec (globalSectionsRing X)))) :=
  rfl

/-- The algebraic space over `S` representing maps to `Spec Γ(X, 𝒪_X)`. -/
def specGamma (X : AlgebraicSpace S) : AlgebraicSpace S :=
  ofOver (specGammaOver X)

/-- `specGamma X` is the representable algebraic space attached to `specGammaOver X`. -/
theorem specGamma_eq (X : AlgebraicSpace S) :
    specGamma X = ofOver (specGammaOver X) :=
  rfl

/-- The projection from the fibre product onto `Spec Γ(X, 𝒪_X)`. -/
def specGamma_fst (X : AlgebraicSpace S) :
    (specGammaOver X).left ⟶ Spec (globalSectionsRing X) :=
  pullback.fst (Over.mk (specULiftZIsTerminal.from (Spec (globalSectionsRing X)))).hom
    (specULiftZIsTerminal.from S)

/-- `specGamma_fst X` is the first projection of the defining pullback. -/
theorem specGamma_fst_eq (X : AlgebraicSpace S) :
    specGamma_fst X =
      pullback.fst (Over.mk (specULiftZIsTerminal.from (Spec (globalSectionsRing X)))).hom
        (specULiftZIsTerminal.from S) :=
  rfl

/-- The scheme morphism from the chosen atlas of `X` to `Spec Γ(X, 𝒪_X)`. -/
def atlasToSpec_scheme (X : AlgebraicSpace S) :
    (chosenPresentation X).U.left ⟶ Spec (globalSectionsRing X) :=
  (chosenPresentation X).U.left.toSpecΓ ≫ Spec.map (globalSectionsRing_ι X)

/-- `atlasToSpec_scheme X` is `U.toSpecΓ` followed by `Spec.map` of the equalizer inclusion. -/
theorem atlasToSpec_scheme_eq (X : AlgebraicSpace S) :
    atlasToSpec_scheme X =
      (chosenPresentation X).U.left.toSpecΓ ≫ Spec.map (globalSectionsRing_ι X) :=
  rfl

/-- The atlas morphism to `Spec Γ(X, 𝒪_X)` is a morphism over `Spec ℤ`. -/
theorem atlasToSpec_scheme_w (X : AlgebraicSpace S) :
    atlasToSpec_scheme X ≫
        (Over.mk (specULiftZIsTerminal.from (Spec (globalSectionsRing X)))).hom =
      ((Over.map (specULiftZIsTerminal.from S)).obj (chosenPresentation X).U).hom :=
  sorry

/-- The atlas of `X`, viewed over `Spec ℤ`, as a morphism to `Spec Γ(X, 𝒪_X)`. -/
def atlasToSpec_overSpecZ (X : AlgebraicSpace S) :
    (Over.map (specULiftZIsTerminal.from S)).obj (chosenPresentation X).U ⟶
      Over.mk (specULiftZIsTerminal.from (Spec (globalSectionsRing X))) :=
  Over.homMk (atlasToSpec_scheme X) (atlasToSpec_scheme_w X)

/-- The underlying scheme morphism of `atlasToSpec_overSpecZ X` is `atlasToSpec_scheme X`. -/
theorem atlasToSpec_overSpecZ_left (X : AlgebraicSpace S) :
    (atlasToSpec_overSpecZ X).left = atlasToSpec_scheme X :=
  rfl

/-- The morphism in `Over S` from the chosen atlas to `specGammaOver X`. -/
def atlasToSpecGammaOver (X : AlgebraicSpace S) :
    (chosenPresentation X).U ⟶ specGammaOver X :=
  ((Over.mapPullbackAdj (specULiftZIsTerminal.from S)).homEquiv
      (chosenPresentation X).U
      (Over.mk (specULiftZIsTerminal.from (Spec (globalSectionsRing X)))))
    (atlasToSpec_overSpecZ X)

/-- `atlasToSpecGammaOver X` is the mate of `atlasToSpec_overSpecZ X`. -/
theorem atlasToSpecGammaOver_eq (X : AlgebraicSpace S) :
    atlasToSpecGammaOver X =
      ((Over.mapPullbackAdj (specULiftZIsTerminal.from S)).homEquiv
          (chosenPresentation X).U
          (Over.mk (specULiftZIsTerminal.from (Spec (globalSectionsRing X)))))
        (atlasToSpec_overSpecZ X) :=
  rfl

/-- The morphism of algebraic spaces from the presenting scheme to `specGamma X`. -/
def atlasToSpecGamma (X : AlgebraicSpace S) :
    ofOver (chosenPresentation X).U ⟶ specGamma X :=
  ofOverMap (atlasToSpecGammaOver X)

/-- `atlasToSpecGamma X` is `ofOverMap` of `atlasToSpecGammaOver X`. -/
theorem atlasToSpecGamma_eq (X : AlgebraicSpace S) :
    atlasToSpecGamma X = ofOverMap (atlasToSpecGammaOver X) :=
  rfl

/-- The two relation projections equalize `atlasToSpecGamma X`. -/
theorem atlasToSpecGamma_equalizes (X : AlgebraicSpace S) :
    ofOverMap (chosenPresentation X).R.t ≫ atlasToSpecGamma X =
      ofOverMap (chosenPresentation X).R.s ≫ atlasToSpecGamma X :=
  sorry

/-- The canonical morphism `X ⟶ Spec Γ(X, 𝒪_X)` over `S`. -/
def toSpecGamma (X : AlgebraicSpace S) : X ⟶ specGamma X :=
  presentationDesc (chosenPresentation X) (atlasToSpecGamma X)
    (atlasToSpecGamma_equalizes X)

/-- `toSpecGamma X` is the descent of `atlasToSpecGamma X` along the chosen presentation. -/
theorem toSpecGamma_eq (X : AlgebraicSpace S) :
    toSpecGamma X =
      presentationDesc (chosenPresentation X) (atlasToSpecGamma X)
        (atlasToSpecGamma_equalizes X) :=
  rfl

/-- Recover a morphism of schemes over `S` from a morphism of the associated algebraic spaces. -/
def ofOverHomPreimage {U V : Over S} (φ : ofOver U ⟶ ofOver V) : U ⟶ V :=
  Yoneda.fullyFaithful.preimage (φ : yoneda.obj U ⟶ yoneda.obj V)

/-- `ofOverHomPreimage φ` is the Yoneda preimage of `φ`. -/
theorem ofOverHomPreimage_eq {U V : Over S} (φ : ofOver U ⟶ ofOver V) :
    ofOverHomPreimage φ =
      Yoneda.fullyFaithful.preimage (φ : yoneda.obj U ⟶ yoneda.obj V) :=
  rfl

/-- The two presentation restrictions of `Y` agree after composing the `ΓSpec` adjunct of
`toSpecGamma` along `f`. -/
theorem globalSectionsRingMap_equalizes {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    ((Scheme.ΓSpecIso (globalSectionsRing X)).inv ≫
          ((ofOverHomPreimage
                ((chosenPresentation Y).atlas ≫ f ≫ toSpecGamma X)).left ≫
            specGamma_fst X).appTop) ≫
        (chosenPresentation Y).tAppTop =
      ((Scheme.ΓSpecIso (globalSectionsRing X)).inv ≫
          ((ofOverHomPreimage
                ((chosenPresentation Y).atlas ≫ f ≫ toSpecGamma X)).left ≫
            specGamma_fst X).appTop) ≫
        (chosenPresentation Y).sAppTop :=
  sorry

/-- The map on global sections `Γ(X, 𝒪_X) ⟶ Γ(Y, 𝒪_Y)` induced by a morphism of algebraic
spaces. -/
def globalSectionsRingMap {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    globalSectionsRing X ⟶ globalSectionsRing Y :=
  equalizer.lift
    ((Scheme.ΓSpecIso (globalSectionsRing X)).inv ≫
      ((ofOverHomPreimage
            ((chosenPresentation Y).atlas ≫ f ≫ toSpecGamma X)).left ≫
        specGamma_fst X).appTop)
    (globalSectionsRingMap_equalizes f)

/-- `globalSectionsRingMap f` lifts the `ΓSpec` adjunct of `Y → Spec Γ(X)` through the
equalizer inclusion of `Γ(Y, 𝒪_Y)`. -/
theorem globalSectionsRingMap_comp_ι {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    globalSectionsRingMap f ≫ globalSectionsRing_ι Y =
      (Scheme.ΓSpecIso (globalSectionsRing X)).inv ≫
        ((ofOverHomPreimage
              ((chosenPresentation Y).atlas ≫ f ≫ toSpecGamma X)).left ≫
          specGamma_fst X).appTop :=
  sorry

/-- The ring presheaf on `(Spaces/X)_étale` with value `Γ(U, 𝒪_U)`. -/
def overEtaleStructurePresheaf (X : AlgebraicSpace S) :
    (Over X)ᵒᵖ ⥤ RingCat.{u} where
  obj U := (forget₂ CommRingCat RingCat).obj (globalSectionsRing U.unop.left)
  map {U V} g :=
    (forget₂ CommRingCat RingCat).map (globalSectionsRingMap g.unop.left)
  map_id _ := sorry
  map_comp _ _ := sorry

/-- The value of `overEtaleStructurePresheaf X` at `U` is `Γ(U.left, 𝒪_{U.left})`. -/
theorem overEtaleStructurePresheaf_obj (X : AlgebraicSpace S) (U : Over X) :
    (overEtaleStructurePresheaf X).obj (op U) =
      (forget₂ CommRingCat RingCat).obj (globalSectionsRing U.left) :=
  rfl

/-- Restriction in `overEtaleStructurePresheaf X` is `globalSectionsRingMap` of the underlying
morphism of algebraic spaces. -/
theorem overEtaleStructurePresheaf_map (X : AlgebraicSpace S) {U V : Over X} (g : U ⟶ V) :
    (overEtaleStructurePresheaf X).map g.op =
      (forget₂ CommRingCat RingCat).map (globalSectionsRingMap g.left) :=
  rfl

/-- The global-sections presheaf on `(Spaces/X)_étale` is a sheaf. -/
theorem overEtaleStructurePresheaf_isSheaf (X : AlgebraicSpace S) :
    Presheaf.IsSheaf (overEtaleTopology X) (overEtaleStructurePresheaf X) :=
  sorry

/-- The structure sheaf `𝒪` on `(Spaces/X)_étale`, with value `U ↦ Γ(U, 𝒪_U)`. -/
def overEtaleStructureSheaf (X : AlgebraicSpace S) :
    Sheaf (overEtaleTopology X) RingCat.{u} :=
  ⟨overEtaleStructurePresheaf X, overEtaleStructurePresheaf_isSheaf X⟩

/-- On an algebraic space `U` over `X`, the big étale structure sheaf has value
`Γ(U, 𝒪_U)`. -/
theorem overEtaleStructureSheaf_obj (X : AlgebraicSpace S) (U : Over X) :
    (overEtaleStructureSheaf X).obj.obj (op U) =
      (forget₂ CommRingCat RingCat).obj (globalSectionsRing U.left) :=
  rfl

/-- Restriction in `overEtaleStructureSheaf X` is `globalSectionsRingMap` of the underlying
morphism of algebraic spaces. -/
theorem overEtaleStructureSheaf_map (X : AlgebraicSpace S) {U V : Over X} (g : U ⟶ V) :
    (overEtaleStructureSheaf X).obj.map g.op =
      (forget₂ CommRingCat RingCat).map (globalSectionsRingMap g.left) :=
  rfl

/-- The big étale ringed site `((Spaces/X)_étale, 𝒪)`. -/
abbrev overEtaleRingedSite (X : AlgebraicSpace S) :=
  RingedSite.ofRingSheaf (overEtaleTopology X) (overEtaleStructureSheaf X)

/-- The structure sheaf of `overEtaleRingedSite X` is `overEtaleStructureSheaf X`. -/
theorem overEtaleRingedSite_structureSheaf (X : AlgebraicSpace S) :
    (overEtaleRingedSite X).structureSheaf = overEtaleStructureSheaf X :=
  rfl

/-- The source-space projection associated to big étale base change along `f`. -/
def bigProjection {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    Over.pullback f ⋙ Over.forget Y ⟶ Over.forget X where
  app U := pullback.fst U.hom f
  naturality _ _ _ := sorry

/-- The projection at `U` is the fibre-product projection `U ×_X Y ⟶ U`. -/
theorem bigProjection_app {X Y : AlgebraicSpace S} (f : Y ⟶ X) (U : Over X) :
    (bigProjection f).app U = pullback.fst U.hom f :=
  rfl

/-- The atlas of `ofOver T` as a morphism of schemes over `S`. -/
def ofOverAtlas (T : Over S) : (chosenPresentation (ofOver T)).U ⟶ T :=
  ofOverHomPreimage (chosenPresentation (ofOver T)).atlas

/-- `ofOverAtlas T` is the Yoneda preimage of the chosen atlas of `ofOver T`. -/
theorem ofOverAtlas_eq (T : Over S) :
    ofOverAtlas T = ofOverHomPreimage (chosenPresentation (ofOver T)).atlas :=
  rfl

/-- The two presentation restrictions of `ofOver T` agree after restriction from `T`. -/
theorem ofOverGlobalSections_equalizes (T : Over S) :
    (ofOverAtlas T).left.appTop ≫ (chosenPresentation (ofOver T)).tAppTop =
      (ofOverAtlas T).left.appTop ≫ (chosenPresentation (ofOver T)).sAppTop :=
  sorry

/-- The identification `Γ(T, 𝒪_T) ⟶ Γ(ofOver T, 𝒪)` on a representable algebraic space. -/
def ofOverGlobalSections (T : Over S) :
    Γ(T.left, ⊤) ⟶ globalSectionsRing (ofOver T) :=
  equalizer.lift (ofOverAtlas T).left.appTop (ofOverGlobalSections_equalizes T)

/-- `ofOverGlobalSections T` lifts restriction along the chosen atlas of `ofOver T`. -/
theorem ofOverGlobalSections_comp_ι (T : Over S) :
    ofOverGlobalSections T ≫ globalSectionsRing_ι (ofOver T) =
      (ofOverAtlas T).left.appTop :=
  sorry

/-- Direct-image form of `i_g^♯`: on a scheme étale over `Y`, the source is `Γ(U, 𝒪_U)`
and the target is `Γ(U, 𝒪_U)` computed as an algebraic space. -/
def relocalizationStructureSheafMap {X Y : AlgebraicSpace S} (g : Y ⟶ X) :
    structureSheaf Y ⟶
      ((relocalizationFunctor g).sheafPushforwardContinuous RingCat.{u}
        (smallEtaleTopology Y) (overEtaleTopology X)).obj
        (overEtaleStructureSheaf X) :=
  ⟨{
    app := fun U ↦
      (forget₂ CommRingCat RingCat).map (ofOverGlobalSections U.unop.left)
    naturality := fun _ _ _ ↦ sorry
  }⟩

/-- The component of `relocalizationStructureSheafMap g` is `ofOverGlobalSections` of the
underlying scheme. -/
theorem relocalizationStructureSheafMap_app {X Y : AlgebraicSpace S} (g : Y ⟶ X)
    (U : (smallEtaleSite Y)ᵒᵖ) :
    (relocalizationStructureSheafMap g).hom.app U =
      (forget₂ CommRingCat RingCat).map (ofOverGlobalSections U.unop.left) :=
  rfl

/-- The structure-sheaf map for postcomposition along `g : Y ⟶ X`. -/
def bigInverseStructureSheafMap {X Y : AlgebraicSpace S} (g : Y ⟶ X) :
    overEtaleStructureSheaf Y ⟶
      ((Over.map g).sheafPushforwardContinuous RingCat.{u}
        (overEtaleTopology Y) (overEtaleTopology X)).obj
        (overEtaleStructureSheaf X) :=
  ⟨{
    app := fun V ↦
      (forget₂ CommRingCat RingCat).map (𝟙 (globalSectionsRing V.unop.left))
    naturality := fun _ _ _ ↦ sorry
  }⟩

/-- The component of `bigInverseStructureSheafMap g` at `V` is the identity on
`Γ(V.left, 𝒪_{V.left})`. -/
theorem bigInverseStructureSheafMap_app {X Y : AlgebraicSpace S} (g : Y ⟶ X)
    (V : (Over Y)ᵒᵖ) :
    (bigInverseStructureSheafMap g).hom.app V =
      (forget₂ CommRingCat RingCat).map (𝟙 (globalSectionsRing V.unop.left)) :=
  rfl

/-- The direct-image-form map on big étale structure sheaves along `f : Y ⟶ X`. -/
def bigStructureSheafMap {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    overEtaleStructureSheaf X ⟶
      ((Over.pullback f).sheafPushforwardContinuous RingCat.{u}
        (overEtaleTopology X) (overEtaleTopology Y)).obj
        (overEtaleStructureSheaf Y) :=
  ⟨{
    app := fun U ↦
      (forget₂ CommRingCat RingCat).map
        (globalSectionsRingMap ((bigProjection f).app U.unop))
    naturality := fun _ _ _ ↦ sorry
  }⟩

/-- The component of `bigStructureSheafMap f` at `U` is the map on global sections along the
fibre-product projection. -/
theorem bigStructureSheafMap_app {X Y : AlgebraicSpace S} (f : Y ⟶ X) (U : (Over X)ᵒᵖ) :
    (bigStructureSheafMap f).hom.app U =
      (forget₂ CommRingCat RingCat).map
        (globalSectionsRingMap ((bigProjection f).app U.unop)) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

namespace AlgebraicGeometry.AlgebraicSpace.Etale.Module

open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The module-sheaf direct image on small étale sites of a morphism of algebraic spaces. -/
abbrev smallDirectImage (f : Y ⟶ X) : Y.Modules ⥤ X.Modules :=
  AlgebraicGeometry.AlgebraicSpace.Modules.pushforward f

/-- `smallDirectImage f` is module pushforward along the associated morphism of ringed topoi. -/
theorem smallDirectImage_eq (f : Y ⟶ X) :
    smallDirectImage f = AlgebraicGeometry.AlgebraicSpace.Modules.pushforward f :=
  rfl

/-- Small étale module pushforward is additive. -/
instance smallDirectImage_additive (f : Y ⟶ X)
    [Preadditive Y.Modules] [Preadditive X.Modules] :
    (smallDirectImage f).Additive :=
  sorry

/-- The module-sheaf direct image on big étale slice sites. -/
def bigDirectImage (f : Y ⟶ X) :
    SheafOfModules.{u} (overEtaleStructureSheaf Y) ⥤
      SheafOfModules.{u} (overEtaleStructureSheaf X) :=
  SheafOfModules.pushforward (bigStructureSheafMap f)

/-- `bigDirectImage f` is module pushforward along `bigStructureSheafMap f`. -/
theorem bigDirectImage_eq (f : Y ⟶ X) :
    bigDirectImage f = SheafOfModules.pushforward (bigStructureSheafMap f) :=
  rfl

/-- Big étale module pushforward is additive. -/
instance bigDirectImage_additive (f : Y ⟶ X)
    [Preadditive (SheafOfModules.{u} (overEtaleStructureSheaf Y))]
    [Preadditive (SheafOfModules.{u} (overEtaleStructureSheaf X))] :
    (bigDirectImage f).Additive :=
  sorry

/-- Exact module restriction from `(Spaces/X)_étale` to the small étale site of `Y`. -/
def relocalization (g : Y ⟶ X) :
    SheafOfModules.{u} (overEtaleStructureSheaf X) ⥤ Y.Modules :=
  SheafOfModules.pushforward (relocalizationStructureSheafMap g)

/-- `relocalization g` is module pushforward along `relocalizationStructureSheafMap g`. -/
theorem relocalization_eq (g : Y ⟶ X) :
    relocalization g = SheafOfModules.pushforward (relocalizationStructureSheafMap g) :=
  rfl

/-- Exact inverse image on big étale module sheaves induced by postcomposition. -/
def bigInverseImage (g : Y ⟶ X) :
    SheafOfModules.{u} (overEtaleStructureSheaf X) ⥤
      SheafOfModules.{u} (overEtaleStructureSheaf Y) :=
  SheafOfModules.pushforward (bigInverseStructureSheafMap g)

/-- `bigInverseImage g` is module pushforward along `bigInverseStructureSheafMap g`. -/
theorem bigInverseImage_eq (g : Y ⟶ X) :
    bigInverseImage g = SheafOfModules.pushforward (bigInverseStructureSheafMap g) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Etale.Module

namespace AlgebraicGeometry.AlgebraicSpace.Etale.Module.Derived

open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The unbounded derived small-site module direct image. -/
noncomputable def smallDirectImage (f : Y ⟶ X)
    [Abelian Y.Modules] [Abelian X.Modules]
    [IsGrothendieckAbelian Y.Modules] [HasDerivedCategory Y.Modules]
    [HasDerivedCategory X.Modules] :
    DerivedCategory Y.Modules ⥤ DerivedCategory X.Modules :=
  Adjunction.Derived.KInjective.right (Module.smallDirectImage f)

/-- Derived small-site module direct image is K-injective total right-derived pushforward. -/
theorem smallDirectImage_eq (f : Y ⟶ X)
    [Abelian Y.Modules] [Abelian X.Modules]
    [IsGrothendieckAbelian Y.Modules] [HasDerivedCategory Y.Modules]
    [HasDerivedCategory X.Modules] :
    smallDirectImage f =
      Adjunction.Derived.KInjective.right (Module.smallDirectImage f) :=
  rfl

/-- The unbounded derived big-site module direct image. -/
noncomputable def bigDirectImage (f : Y ⟶ X)
    [Abelian (SheafOfModules.{u} (overEtaleStructureSheaf Y))]
    [Abelian (SheafOfModules.{u} (overEtaleStructureSheaf X))]
    [IsGrothendieckAbelian (SheafOfModules.{u} (overEtaleStructureSheaf Y))]
    [HasDerivedCategory (SheafOfModules.{u} (overEtaleStructureSheaf Y))]
    [HasDerivedCategory (SheafOfModules.{u} (overEtaleStructureSheaf X))] :
    DerivedCategory (SheafOfModules.{u} (overEtaleStructureSheaf Y)) ⥤
      DerivedCategory (SheafOfModules.{u} (overEtaleStructureSheaf X)) :=
  Adjunction.Derived.KInjective.right (Module.bigDirectImage f)

/-- Derived big-site module direct image is K-injective total right-derived pushforward. -/
theorem bigDirectImage_eq (f : Y ⟶ X)
    [Abelian (SheafOfModules.{u} (overEtaleStructureSheaf Y))]
    [Abelian (SheafOfModules.{u} (overEtaleStructureSheaf X))]
    [IsGrothendieckAbelian (SheafOfModules.{u} (overEtaleStructureSheaf Y))]
    [HasDerivedCategory (SheafOfModules.{u} (overEtaleStructureSheaf Y))]
    [HasDerivedCategory (SheafOfModules.{u} (overEtaleStructureSheaf X))] :
    bigDirectImage f =
      Adjunction.Derived.KInjective.right (Module.bigDirectImage f) :=
  rfl

/-- The exact module restriction from a big étale site to a small étale site. -/
noncomputable def relocalizationExact (g : Y ⟶ X) :
    SheafOfModules.{u} (overEtaleStructureSheaf X) ⥤ₑ Y.Modules :=
  ⟨Module.relocalization g, sorry⟩

/-- The derived module restriction from `(Spaces/X)_étale` to `Y_étale`. -/
noncomputable def relocalization (g : Y ⟶ X)
    [Abelian (SheafOfModules.{u} (overEtaleStructureSheaf X))] [Abelian Y.Modules]
    [HasDerivedCategory (SheafOfModules.{u} (overEtaleStructureSheaf X))]
    [HasDerivedCategory Y.Modules] :
    DerivedCategory (SheafOfModules.{u} (overEtaleStructureSheaf X)) ⥤
      DerivedCategory Y.Modules :=
  (relocalizationExact g).mapDerivedCategory

/-- Derived relocalization is the derived functor of the exact module restriction. -/
theorem relocalization_eq (g : Y ⟶ X)
    [Abelian (SheafOfModules.{u} (overEtaleStructureSheaf X))] [Abelian Y.Modules]
    [HasDerivedCategory (SheafOfModules.{u} (overEtaleStructureSheaf X))]
    [HasDerivedCategory Y.Modules] :
    relocalization g = (relocalizationExact g).mapDerivedCategory :=
  rfl

/-- The exact big-site module inverse image along postcomposition. -/
noncomputable def bigInverseImageExact (g : Y ⟶ X) :
    SheafOfModules.{u} (overEtaleStructureSheaf X) ⥤ₑ
      SheafOfModules.{u} (overEtaleStructureSheaf Y) :=
  ⟨Module.bigInverseImage g, sorry⟩

/-- The derived big-site module inverse image along postcomposition. -/
noncomputable def bigInverseImage (g : Y ⟶ X)
    [Abelian (SheafOfModules.{u} (overEtaleStructureSheaf X))]
    [Abelian (SheafOfModules.{u} (overEtaleStructureSheaf Y))]
    [HasDerivedCategory (SheafOfModules.{u} (overEtaleStructureSheaf X))]
    [HasDerivedCategory (SheafOfModules.{u} (overEtaleStructureSheaf Y))] :
    DerivedCategory (SheafOfModules.{u} (overEtaleStructureSheaf X)) ⥤
      DerivedCategory (SheafOfModules.{u} (overEtaleStructureSheaf Y)) :=
  (bigInverseImageExact g).mapDerivedCategory

/-- Derived big inverse image is the derived functor of the exact postcomposition inverse image. -/
theorem bigInverseImage_eq (g : Y ⟶ X)
    [Abelian (SheafOfModules.{u} (overEtaleStructureSheaf X))]
    [Abelian (SheafOfModules.{u} (overEtaleStructureSheaf Y))]
    [HasDerivedCategory (SheafOfModules.{u} (overEtaleStructureSheaf X))]
    [HasDerivedCategory (SheafOfModules.{u} (overEtaleStructureSheaf Y))] :
    bigInverseImage g = (bigInverseImageExact g).mapDerivedCategory :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Etale.Module.Derived

end
