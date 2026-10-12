/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.EffectiveEpi.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.RingedSite.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived
public import ReasLib.AlgebraicGeometry.RingedSite.Module.InverseImage.Exact
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.Sites.MorphismOfSites
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Definition_66_29_1_RingedSite
public import stacks_project.Chap69.Situation_69_16_1_GlobalSections
public import stacks_project.Chap84.Lemma_84_5_5_SmallToBig

/-!
# Big étale ringed site of an algebraic space

The structure sheaf `𝒪` on `(Spaces/X)_étale` is the global-sections sheaf
`U ↦ Γ(U, 𝒪_U)`, not `π_X⁻¹ 𝒪_X`. Restriction is the equalizer-lift of the
scheme-level map on the chosen atlas.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open CategoryTheory.EffectiveEpi
open RingedSite.Hom
open RingedSite.Cocontinuous

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale

variable {S : Scheme.{u}}

/-- Relocalization is a morphism of sites from the small étale site to the big étale slice. -/
instance relocalizationFunctor_isMorphismOfSites {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    IsMorphismOfSites (smallEtaleTopology Y) (overEtaleTopology X)
      (relocalizationFunctor f) :=
  sorry

/-- Recover a morphism of schemes over `S` from a morphism of the associated algebraic spaces. -/
def ofOverHomPreimage {U V : Over S} (φ : ofOver U ⟶ ofOver V) : U ⟶ V :=
  Yoneda.fullyFaithful.preimage (φ : yoneda.obj U ⟶ yoneda.obj V)

/-- The atlas of `ofOver T` as a morphism of schemes over `S`. -/
def ofOverAtlas (T : Over S) : (chosenPresentation (ofOver T)).U ⟶ T :=
  ofOverHomPreimage (chosenPresentation (ofOver T)).atlas

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

/-- The scheme morphism from the chosen atlas of `X` to `Spec Γ(X, 𝒪_X)` classified by the
equalizer inclusion `Γ(X, 𝒪_X) ⟶ Γ(U, 𝒪_U)`. -/
def atlasToSpec_scheme (X : AlgebraicSpace S) :
    (chosenPresentation X).U.left ⟶ Spec (globalSectionsRing X) :=
  (chosenPresentation X).U.left.toSpecΓ ≫ Spec.map (globalSectionsRing_ι X)

/-- `atlasToSpec_scheme X` is `U.toSpecΓ` followed by `Spec.map` of the equalizer inclusion. -/
theorem atlasToSpec_scheme_eq (X : AlgebraicSpace S) :
    atlasToSpec_scheme X =
      (chosenPresentation X).U.left.toSpecΓ ≫ Spec.map (globalSectionsRing_ι X) :=
  rfl

/-- The atlas of `Y`, viewed as a morphism of sheaves into `X`. -/
def atlasToX {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    yoneda.obj (chosenPresentation Y).U ⟶ X.functorOfPoints :=
  (chosenPresentation Y).atlas ≫ f

/-- `atlasToX f` is the chosen atlas of `Y` composed with `f`. -/
theorem atlasToX_eq {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    atlasToX f = (chosenPresentation Y).atlas ≫ f :=
  rfl

/-- The fibre product of the chosen atlas of `Y` with the chosen atlas of `X`. -/
def atlasPullback {X Y : AlgebraicSpace S} (f : Y ⟶ X) : Over S :=
  (chosenPresentation X).atlas_etale.rep.pullback (atlasToX f)

/-- Projection from the atlas fibre product to the chosen atlas of `Y`. -/
def atlasPullbackToY {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    atlasPullback f ⟶ (chosenPresentation Y).U :=
  (chosenPresentation X).atlas_etale.rep.snd (atlasToX f)

/-- Projection from the atlas fibre product to the chosen atlas of `X`. -/
def atlasPullbackToX {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    atlasPullback f ⟶ (chosenPresentation X).U :=
  (chosenPresentation X).atlas_etale.rep.fst' (atlasToX f)

/-- The underlying scheme morphism of `atlasPullbackToY f`. -/
def atlasPullbackToYScheme {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    (atlasPullback f).left ⟶ (chosenPresentation Y).U.left :=
  (atlasPullbackToY f).left

/-- The underlying scheme morphism of `atlasPullbackToX f`. -/
def atlasPullbackToXScheme {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    (atlasPullback f).left ⟶ (chosenPresentation X).U.left :=
  (atlasPullbackToX f).left

/-- `atlasPullbackToYScheme f` is étale. -/
instance atlasPullbackToYScheme_etale {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    _root_.AlgebraicGeometry.Etale (atlasPullbackToYScheme f) :=
  (chosenPresentation X).atlas_etale.property_snd (atlasToX f)

/-- `atlasPullbackToYScheme f` is surjective. -/
instance atlasPullbackToYScheme_surjective {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    _root_.AlgebraicGeometry.Surjective (atlasPullbackToYScheme f) :=
  sorry

/-- The scheme morphism from the atlas fibre product to `Spec Γ(X, 𝒪_X)`. -/
def atlasPullbackToSpecGamma {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    (atlasPullback f).left ⟶ Spec (globalSectionsRing X) :=
  atlasPullbackToXScheme f ≫ atlasToSpec_scheme X

/-- `atlasPullbackToSpecGamma f` is `atlasPullbackToX f` followed by `atlasToSpec_scheme X`. -/
theorem atlasPullbackToSpecGamma_eq {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    atlasPullbackToSpecGamma f =
      (atlasPullbackToX f).left ≫ atlasToSpec_scheme X :=
  rfl

/-- Morphisms that equalize `atlasPullbackToY f` also equalize `atlasPullbackToSpecGamma f`. -/
theorem atlasPullbackToSpecGamma_descends {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ (atlasPullback f).left)
    (hg : g₁ ≫ atlasPullbackToYScheme f = g₂ ≫ atlasPullbackToYScheme f) :
    g₁ ≫ atlasPullbackToSpecGamma f = g₂ ≫ atlasPullbackToSpecGamma f :=
  sorry

/-- The scheme morphism from the chosen atlas of `Y` to `Spec Γ(X, 𝒪_X)`, obtained by
descending the atlas fibre product along the étale surjection `atlasPullbackToY f`. -/
def atlasYToSpecGamma {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    (chosenPresentation Y).U.left ⟶ Spec (globalSectionsRing X) :=
  EffectiveEpi.desc (atlasPullbackToYScheme f) (atlasPullbackToSpecGamma f)
    (atlasPullbackToSpecGamma_descends f)

/-- `atlasYToSpecGamma f` is the effective-epi descent of `atlasPullbackToSpecGamma f`. -/
theorem atlasYToSpecGamma_eq {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    atlasYToSpecGamma f =
      EffectiveEpi.desc (atlasPullbackToYScheme f) (atlasPullbackToSpecGamma f)
        (atlasPullbackToSpecGamma_descends f) :=
  rfl

/-- Scheme-level restriction `Γ(X) ⟶ Γ(U_Y)` along `f`, as `ΓSpecIso.inv` followed by
`appTop` of the descended map from the chosen atlas of `Y` to `Spec Γ(X)`. -/
def globalSectionsToYAtlas {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    globalSectionsRing X ⟶ Γ((chosenPresentation Y).U.left, ⊤) :=
  (Scheme.ΓSpecIso (globalSectionsRing X)).inv ≫ (atlasYToSpecGamma f).appTop

/-- `globalSectionsToYAtlas f` is the `ΓSpec` adjunct of `atlasYToSpecGamma f`. -/
theorem globalSectionsToYAtlas_eq {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    globalSectionsToYAtlas f =
      (Scheme.ΓSpecIso (globalSectionsRing X)).inv ≫ (atlasYToSpecGamma f).appTop :=
  rfl

/-- The two presentation restrictions of `Y` agree after the scheme-level atlas
restriction from `X`. -/
theorem globalSectionsRingMap_equalizes {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    globalSectionsToYAtlas f ≫ (chosenPresentation Y).tAppTop =
      globalSectionsToYAtlas f ≫ (chosenPresentation Y).sAppTop :=
  sorry

/-- The map on global sections `Γ(X, 𝒪_X) ⟶ Γ(Y, 𝒪_Y)` induced by a morphism of algebraic
spaces, as the equalizer lift of the scheme-level map into Gamma of the chosen atlas
of `Y`. -/
def globalSectionsRingMap {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    globalSectionsRing X ⟶ globalSectionsRing Y :=
  equalizer.lift (globalSectionsToYAtlas f) (globalSectionsRingMap_equalizes f)

/-- `globalSectionsRingMap f` lifts `globalSectionsToYAtlas f` through the equalizer
inclusion of `Γ(Y, 𝒪_Y)`. -/
theorem globalSectionsRingMap_comp_ι {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    globalSectionsRingMap f ≫ globalSectionsRing_ι Y = globalSectionsToYAtlas f :=
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
abbrev overEtaleRingedSite (X : AlgebraicSpace S) : RingedSite.{u + 1, u + 1, u} :=
  RingedSite.ofRingSheaf (overEtaleTopology X) (overEtaleStructureSheaf X)

/-- The structure sheaf of `overEtaleRingedSite X` is `overEtaleStructureSheaf X`. -/
theorem overEtaleRingedSite_structureSheaf (X : AlgebraicSpace S) :
    (overEtaleRingedSite X).structureSheaf = overEtaleStructureSheaf X :=
  rfl

/-- Direct-image form of `π_X^♯` / `i_f^♯`: on a scheme étale over `Y`, the source is
`Γ(U, 𝒪_U)` and the target is `Γ(U, 𝒪_U)` computed as an algebraic space. -/
def smallToBigStructureSheafMap {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    structureSheaf Y ⟶
      ((relocalizationFunctor f).sheafPushforwardContinuous RingCat.{u}
        (smallEtaleTopology Y) (overEtaleTopology X)).obj
        (overEtaleStructureSheaf X) :=
  InducedCategory.homMk
    { app := fun U ↦
        (forget₂ CommRingCat RingCat).map (ofOverGlobalSections U.unop.left)
      naturality := fun _ _ _ ↦ sorry }

/-- The component of `smallToBigStructureSheafMap f` is `ofOverGlobalSections` of the
underlying scheme. -/
theorem smallToBigStructureSheafMap_app {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (U : (smallEtaleSite Y)ᵒᵖ) :
    (smallToBigStructureSheafMap f).hom.app U =
      (forget₂ CommRingCat RingCat).map (ofOverGlobalSections U.unop.left) :=
  rfl

/-- The morphism of ringed sites `π_X : ((Spaces/X)_étale, 𝒪) ⟶ (X_étale, 𝒪_X)`, with
structure map the small-site identification `(π_* 𝒪)(U) = Γ(U, 𝒪_U) = 𝒪_X(U)`. -/
def etalePiRingedHom (X : AlgebraicSpace S) :
    RingedSite.Hom (overEtaleRingedSite X) (ringedSite X) where
  base := relocalizationFunctor (𝟙 X)
  structureSheafMap := smallToBigStructureSheafMap (𝟙 X)

/-- The base functor of `etalePiRingedHom X` is identity-base étale relocalization. -/
theorem etalePiRingedHom_base (X : AlgebraicSpace S) :
    (etalePiRingedHom X).base = relocalizationFunctor (𝟙 X) :=
  rfl

/-- The structure-sheaf map of `etalePiRingedHom X` is `smallToBigStructureSheafMap (𝟙 X)`. -/
theorem etalePiRingedHom_structureSheafMap (X : AlgebraicSpace S) :
    (etalePiRingedHom X).structureSheafMap = smallToBigStructureSheafMap (𝟙 X) :=
  rfl

/-- The morphism of ringed sites `i_f : (Y_étale, 𝒪_Y) ⟶ ((Spaces/X)_étale, 𝒪)`, with
structure map the identification `i_f^{-1} 𝒪 ≅ 𝒪_Y`. -/
def relocalizationRingedHom {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    RingedSite.Hom (overEtaleRingedSite X) (ringedSite Y) where
  base := relocalizationFunctor f
  structureSheafMap := smallToBigStructureSheafMap f

/-- The base functor of `relocalizationRingedHom f` is étale relocalization along `f`. -/
theorem relocalizationRingedHom_base {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    (relocalizationRingedHom f).base = relocalizationFunctor f :=
  rfl

/-- The structure-sheaf map of `relocalizationRingedHom f` is `smallToBigStructureSheafMap f`. -/
theorem relocalizationRingedHom_structureSheafMap {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    (relocalizationRingedHom f).structureSheafMap = smallToBigStructureSheafMap f :=
  rfl

/-- Underlying module inverse image `i_f^*` with coefficients `𝒪_Y`, via `i_f^♯`. -/
noncomputable def relocalizationModuleFunctor {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    RingedSite.ModuleCat.{u + 1} (overEtaleRingedSite X) ⥤
      RingedSite.ModuleCat.{u + 1} (ringedSite Y) :=
  moduleInverseImage (relocalizationFunctor f) (overEtaleStructureSheaf X) ⋙
    SheafOfModules.restrictScalars.{u + 1} (smallToBigStructureSheafMap f)

/-- `relocalizationModuleFunctor f` is module inverse image along `i_f` followed by
restriction of scalars along `i_f^♯`. -/
theorem relocalizationModuleFunctor_eq {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    relocalizationModuleFunctor f =
      moduleInverseImage (relocalizationFunctor f) (overEtaleStructureSheaf X) ⋙
        SheafOfModules.restrictScalars.{u + 1} (smallToBigStructureSheafMap f) :=
  rfl

/-- `relocalizationModuleFunctor f` preserves finite limits. -/
instance relocalizationModuleFunctor_preservesFiniteLimits {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) :
    PreservesFiniteLimits (relocalizationModuleFunctor f) :=
  sorry

/-- `relocalizationModuleFunctor f` preserves finite colimits. -/
instance relocalizationModuleFunctor_preservesFiniteColimits {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) :
    PreservesFiniteColimits (relocalizationModuleFunctor f) :=
  sorry

/-- Derived inverse image `i_f^* : D((Spaces/X)_étale, 𝒪) ⥤ D(Y_étale, 𝒪_Y)`. -/
noncomputable def relocalizationModuleDerived {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [UnivLE.{u + 1, u + 1}] :
    ModuleDerived.{u + 1} (overEtaleRingedSite X) ⥤
      ModuleDerived.{u + 1} (ringedSite Y) :=
  @ExactFunctor.mapDerivedCategory
    (RingedSite.ModuleCat.{u + 1} (overEtaleRingedSite X)) _ _
    (moduleCat_hasDerivedCategory (overEtaleRingedSite X))
    (RingedSite.ModuleCat.{u + 1} (ringedSite Y)) _ _
    (moduleCat_hasDerivedCategory (ringedSite Y))
    (ExactFunctor.of (relocalizationModuleFunctor f))

/-- Source identity: `Lf_small^*` is `i_f^* ∘ Lπ_X^*`. -/
noncomputable def etaleSmallModulePullbackDerived {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [UnivLE.{u + 1, u + 1}]
    [(etalePiRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{u + 1} (etalePiRingedHom X))
      (ModuleQis.{u + 1} (ringedSite X))] :
    ModuleDerived.{u + 1} (ringedSite X) ⥤ ModuleDerived.{u + 1} (ringedSite Y) :=
  modulePullbackDerived.{u + 1} (etalePiRingedHom X) ⋙ relocalizationModuleDerived f

/-- `etaleSmallModulePullbackDerived f` is the composite `i_f^* ∘ Lπ_X^*`. -/
theorem etaleSmallModulePullbackDerived_eq {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [UnivLE.{u + 1, u + 1}]
    [(etalePiRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{u + 1} (etalePiRingedHom X))
      (ModuleQis.{u + 1} (ringedSite X))] :
    etaleSmallModulePullbackDerived f =
      modulePullbackDerived.{u + 1} (etalePiRingedHom X) ⋙
        relocalizationModuleDerived f :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Etale
