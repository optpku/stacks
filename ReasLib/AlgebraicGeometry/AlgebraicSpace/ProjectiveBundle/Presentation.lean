/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.Presentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ProjectiveBundle.Lift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InvertibleQuotient.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Glueing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion

/-!
# Symmetric presentations of projective bundles of algebraic spaces

A symmetric presentation of `π : 𝐏(ℰ) ⟶ X` is an étale-local scheme-level
symmetric presentation of the relative projective bundle of `ℰ`. The tautological
invertible quotient `π^* ℰ ⟶ 𝒪(1)` is stored on the total space and compared with
the scheme tautological quotient along the chart.
-/

@[expose] public section

-- Public constructions unfold private chart computations without publishing those helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory.isInvertibleObject
open CategoryTheory.InvertibleQuotient hiding pullback pullbackClass pullbackMap_epi pullback_rel
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry
namespace AlgebraicSpace
namespace ProjectiveBundle

variable {S : Scheme.{u}} {X P : AlgebraicSpace S} {ℰ : X.Modules} [hℰ : ℰ.IsQuasicoherent]

private def sourceRestrictionIso {π : P ⟶ X} (atlas : smallEtaleSite X)
    (localScheme : Scheme.{u}) (localπ : localScheme ⟶ atlas.left.left)
    (localIso : etaleBaseChangeSpace π atlas ≅
      ofOver (Over.mk (localπ ≫ atlas.left.hom)))
    (localCover_π : (localIso.inv ≫ etaleBaseChangeHom π atlas) ≫ π =
      ofOverMap (Over.homMk localπ rfl) ≫ atlas.hom)
    (localℰ : atlas.left.left.Modules)
    (localℰIso : (Modules.restrictToScheme atlas.left).obj
      ((Modules.pullback atlas.hom).obj ℰ) ≅ localℰ) :
    (Modules.restrictToScheme (Over.mk (localπ ≫ atlas.left.hom))).obj
      ((Modules.pullback (localIso.inv ≫ etaleBaseChangeHom π atlas)).obj
        ((Modules.pullback π).obj ℰ)) ≅
      (Scheme.Modules.pullback localπ).obj localℰ :=
  ((Modules.restrictToScheme (Over.mk (localπ ≫ atlas.left.hom))).mapIso
          ((Modules.pullbackCompIso (localIso.inv ≫ etaleBaseChangeHom π atlas) π).app ℰ) ≪≫
        (Modules.restrictToScheme (Over.mk (localπ ≫ atlas.left.hom))).mapIso
          (eqToIso (congrArg (fun h ↦ (Modules.pullback h).obj ℰ) localCover_π)) ≪≫
        (@Modules.RestrictToScheme.compositePullbackIso S X
          (Over.mk (localπ ≫ atlas.left.hom)) atlas.left atlas.hom
          (Over.homMk localπ rfl) ℰ hℰ).symm ≪≫
        (Scheme.Modules.pullback localπ).mapIso localℰIso)

private def sourceRestrictionHom {π : P ⟶ X} (atlas : smallEtaleSite X)
    (localScheme : Scheme.{u}) (localπ : localScheme ⟶ atlas.left.left)
    (localIso : etaleBaseChangeSpace π atlas ≅
      ofOver (Over.mk (localπ ≫ atlas.left.hom)))
    (localCover_π : (localIso.inv ≫ etaleBaseChangeHom π atlas) ≫ π =
      ofOverMap (Over.homMk localπ rfl) ≫ atlas.hom)
    (localℰ : atlas.left.left.Modules)
    (localℰIso : (Modules.restrictToScheme atlas.left).obj
      ((Modules.pullback atlas.hom).obj ℰ) ≅ localℰ) :
    (Modules.restrictToScheme (Over.mk (localπ ≫ atlas.left.hom))).obj
      ((Modules.pullback (localIso.inv ≫ etaleBaseChangeHom π atlas)).obj
        ((Modules.pullback π).obj ℰ)) ⟶
      (Scheme.Modules.pullback localπ).obj localℰ :=
  (sourceRestrictionIso (ℰ := ℰ) atlas localScheme localπ localIso localCover_π localℰ localℰIso).hom

private def restrictionCondition {π : P ⟶ X} (atlas : smallEtaleSite X)
    (localScheme : Scheme.{u}) (localπ : localScheme ⟶ atlas.left.left)
    (localIso : etaleBaseChangeSpace π atlas ≅
      ofOver (Over.mk (localπ ≫ atlas.left.hom)))
    (localCover_π : (localIso.inv ≫ etaleBaseChangeHom π atlas) ≫ π =
      ofOverMap (Over.homMk localπ rfl) ≫ atlas.hom)
    (localℰ : atlas.left.left.Modules)
    (localℰIso : (Modules.restrictToScheme atlas.left).obj
      ((Modules.pullback atlas.hom).obj ℰ) ≅ localℰ)
    (localPresentation : Scheme.ProjectiveBundle.SymmetricPresentation localπ localℰ)
    (tautologicalTarget : P.Modules)
    (tautologicalHom : (Modules.pullback π).obj ℰ ⟶ tautologicalTarget)
    (tautologicalRestrictIso :
      (Modules.restrictToScheme (Over.mk (localπ ≫ atlas.left.hom))).obj
        ((Modules.pullback (localIso.inv ≫ etaleBaseChangeHom π atlas)).obj
          tautologicalTarget) ≅ localPresentation.tautologicalTarget) : Prop :=
  (Modules.restrictToScheme (Over.mk (localπ ≫ atlas.left.hom))).map
    ((Modules.pullback (localIso.inv ≫ etaleBaseChangeHom π atlas)).map
      tautologicalHom) ≫ tautologicalRestrictIso.hom =
    sourceRestrictionHom (ℰ := ℰ) atlas localScheme localπ localIso localCover_π
      localℰ localℰIso ≫ localPresentation.tautologicalMap

set_option maxHeartbeats 400000 in
/-- An étale-local scheme symmetric presentation of a projective bundle `π : 𝐏(ℰ) ⟶ X`. -/
structure SymmetricPresentation (π : P ⟶ X) (ℰ : X.Modules) [hℰ : ℰ.IsQuasicoherent] where
  /-- An étale atlas of the base algebraic space. -/
  atlas : smallEtaleSite X
  /-- The atlas is étale-locally surjective. -/
  atlas_locallySurjective :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) atlas.hom
  /-- The scheme `𝐏(ℰ|_U)` covering the total space étale-locally. -/
  localScheme : Scheme.{u}
  /-- The structure morphism of the local scheme projective bundle. -/
  localπ : localScheme ⟶ atlas.left.left
  /-- Base change of `π` along the atlas is the local scheme projective bundle. -/
  localIso :
    etaleBaseChangeSpace π atlas ≅
      ofOver (Over.mk (localπ ≫ atlas.left.hom))
  /-- The comparison identifies the projection to the atlas with the local structure morphism. -/
  localIso_snd :
    localIso.hom ≫ ofOverMap (Over.homMk localπ rfl) = etaleBaseChangeSnd π atlas
  /-- The covering morphism composed with `π` is the atlas projection of the local bundle. -/
  localCover_π :
    (localIso.inv ≫ etaleBaseChangeHom π atlas) ≫ π =
      ofOverMap (Over.homMk localπ rfl) ≫ atlas.hom
  /-- The quasi-coherent module on the atlas scheme corresponding to `ℰ`. -/
  localℰ : atlas.left.left.Modules
  /-- Quasi-coherence of the atlas-scheme module. -/
  localℰ_isQuasicoherent : localℰ.IsQuasicoherent
  /-- Restriction of the pulled-back module to the atlas scheme recovers `localℰ`. -/
  localℰIso :
    (Modules.restrictToScheme atlas.left).obj ((Modules.pullback atlas.hom).obj ℰ) ≅
      localℰ
  /-- The scheme-level symmetric presentation of `localπ : 𝐏(localℰ) ⟶ U`. -/
  localPresentation :
    AlgebraicGeometry.Scheme.ProjectiveBundle.SymmetricPresentation localπ localℰ
  /-- The tautological first twist `𝒪(1)` on the total space. -/
  tautologicalTarget : P.Modules
  /-- The tautological first twist is invertible. -/
  tautological_isInvertible : isInvertibleObject tautologicalTarget
  /-- The tautological quotient morphism `π^* ℰ ⟶ 𝒪(1)`. -/
  tautologicalHom : (Modules.pullback π).obj ℰ ⟶ tautologicalTarget
  /-- Restriction of the tautological first twist recovers the scheme tautological target. -/
  tautologicalRestrictIso :
    (Modules.restrictToScheme (Over.mk (localπ ≫ atlas.left.hom))).obj
        ((Modules.pullback (localIso.inv ≫ etaleBaseChangeHom π atlas)).obj
          tautologicalTarget) ≅
      localPresentation.tautologicalTarget
  /-- The chart restriction of `tautologicalHom`, transported by `tautologicalRestrictIso`
  and `localSourceRestrictIso`, is the scheme tautological quotient map. -/
  tautologicalHom_restrict :
    AlgebraicGeometry.AlgebraicSpace.ProjectiveBundle.restrictionCondition
      (ℰ := ℰ) atlas localScheme localπ localIso localCover_π localℰ localℰIso
      localPresentation tautologicalTarget tautologicalHom tautologicalRestrictIso

namespace SymmetricPresentation

set_option maxHeartbeats 400000 in
/-- Construct a symmetric presentation from an étale chart comparison with a scheme
symmetric presentation, together with the stored tautological quotient and its
restriction square. -/
def of {π : P ⟶ X}
    (atlas : smallEtaleSite X)
    (atlas_locallySurjective :
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) atlas.hom)
    (localScheme : Scheme.{u}) (localπ : localScheme ⟶ atlas.left.left)
    (localIso :
      etaleBaseChangeSpace π atlas ≅
        ofOver (Over.mk (localπ ≫ atlas.left.hom)))
    (localIso_snd :
      localIso.hom ≫ ofOverMap (Over.homMk localπ rfl) = etaleBaseChangeSnd π atlas)
    (localCover_π :
      (localIso.inv ≫ etaleBaseChangeHom π atlas) ≫ π =
        ofOverMap (Over.homMk localπ rfl) ≫ atlas.hom)
    (localℰ : atlas.left.left.Modules)
    (localℰ_isQuasicoherent : localℰ.IsQuasicoherent)
    (localℰIso :
      (Modules.restrictToScheme atlas.left).obj ((Modules.pullback atlas.hom).obj ℰ) ≅
        localℰ)
    (localPresentation :
      AlgebraicGeometry.Scheme.ProjectiveBundle.SymmetricPresentation localπ localℰ)
    (tautologicalTarget : P.Modules)
    (tautological_isInvertible : isInvertibleObject tautologicalTarget)
    (tautologicalHom : (Modules.pullback π).obj ℰ ⟶ tautologicalTarget)
    (tautologicalRestrictIso :
      (Modules.restrictToScheme (Over.mk (localπ ≫ atlas.left.hom))).obj
          ((Modules.pullback (localIso.inv ≫ etaleBaseChangeHom π atlas)).obj
            tautologicalTarget) ≅
        localPresentation.tautologicalTarget)
    (tautologicalHom_restrict :
      AlgebraicGeometry.AlgebraicSpace.ProjectiveBundle.restrictionCondition
        (ℰ := ℰ) atlas localScheme localπ localIso localCover_π localℰ localℰIso
        localPresentation tautologicalTarget tautologicalHom tautologicalRestrictIso) :
        SymmetricPresentation π ℰ :=
  { atlas
    atlas_locallySurjective
    localScheme
    localπ
    localIso
    localIso_snd
    localCover_π
    localℰ
    localℰ_isQuasicoherent
    localℰIso
    localPresentation
    tautologicalTarget
    tautological_isInvertible
    tautologicalHom
    tautologicalRestrictIso
    tautologicalHom_restrict }

variable {π : P ⟶ X} (Pres : SymmetricPresentation π ℰ)

/-- The covering morphism `𝐏(ℰ|_U) ⟶ 𝐏(ℰ)` from the local scheme. -/
def localCoverHom : ofOver (Over.mk (Pres.localπ ≫ Pres.atlas.left.hom)) ⟶ P :=
  Pres.localIso.inv ≫ etaleBaseChangeHom π Pres.atlas

/-- The canonical tautological invertible quotient `π^* ℰ ⟶ 𝒪(1)`. -/
def tautologicalQuotient :
    InvertibleQuotient ((Modules.pullback π).obj ℰ) where
  object := Pres.tautologicalTarget
  isInvertible := Pres.tautological_isInvertible
  hom := Pres.tautologicalHom
  hom_epi := sorry

/-- The tautological quotient has its specified target and morphism. -/
theorem tautologicalQuotient_spec :
    Pres.tautologicalQuotient.object = Pres.tautologicalTarget ∧
      Pres.tautologicalQuotient.hom = Pres.tautologicalHom := ⟨rfl, rfl⟩

/-- Restriction of the tautological source is induced by composition of pullbacks and
restriction of the module to the base chart. -/
def localSourceRestrictIso :
    (Modules.restrictToScheme (Over.mk (Pres.localπ ≫ Pres.atlas.left.hom))).obj
        ((Modules.pullback Pres.localCoverHom).obj ((Modules.pullback π).obj ℰ)) ≅
      (Scheme.Modules.pullback Pres.localπ).obj Pres.localℰ :=
  AlgebraicGeometry.AlgebraicSpace.ProjectiveBundle.sourceRestrictionIso (ℰ := ℰ) Pres.atlas Pres.localScheme Pres.localπ Pres.localIso
    Pres.localCover_π Pres.localℰ Pres.localℰIso

/-- The concrete quotient on a test algebraic space obtained by pulling back the tautological
quotient along a lift and transporting its source through the lift triangle. -/
def liftSourceQuotient {T : AlgebraicSpace S} {f : T ⟶ X} (σ : Lift π f) :
    InvertibleQuotient ((Modules.pullback f).obj ℰ) :=
  precomposeIso (Lift.pullbackSourceIso σ ℰ).symm
    (AlgebraicSpace.InvertibleQuotient.pullback σ.hom Pres.tautologicalQuotient)

/-- The value of the invertible-quotient-class functor at a test morphism. -/
abbrev QuotientPoint (ℰ : X.Modules) {T : AlgebraicSpace S} (f : T ⟶ X) :=
  IsoClass ((Modules.pullback f).obj ℰ)

/-- Pull back an invertible-quotient class along a morphism of test algebraic spaces, with
the canonical comparison identifying successive pullback with pullback along the composite. -/
def quotientPointMap {T R : AlgebraicSpace S} (f : T ⟶ X) (g : R ⟶ T) :
    QuotientPoint ℰ f → QuotientPoint ℰ (g ≫ f) := fun q ↦
  precomposeIsoClass ((Modules.pullbackCompIso g f).app ℰ).symm (AlgebraicSpace.InvertibleQuotient.pullbackClass g q)

/-- The quotient class obtained by pulling back the concrete tautological quotient along a
lift. -/
def liftToQuotientClass {T : AlgebraicSpace S} (f : T ⟶ X) :
    Lift π f → QuotientPoint ℰ f := fun σ ↦
  IsoClass.mk (Pres.liftSourceQuotient σ)

/-- The quotient class associated to a section, transported through identity pullback. -/
def sectionToQuotientClass :
    Lift π (𝟙 X) → IsoClass ℰ := fun σ ↦
  isoClassEquivOfIso ((SmallEtaleModuleGlueing.modulesPullbackId X).app ℰ)
    (Pres.liftToQuotientClass (𝟙 X) σ)

/-- The lift-to-quotient-class correspondence is bijective for every test morphism. -/
theorem liftToQuotientClass_bijective {T : AlgebraicSpace S} (f : T ⟶ X) :
    Function.Bijective (Pres.liftToQuotientClass f) := sorry

/-- Sections of a symmetric projective bundle of a quasi-coherent
module `ℰ` on an algebraic space correspond bijectively to invertible quotient classes
of `ℰ`. -/
theorem sectionToQuotientClass_bijective (Pres : SymmetricPresentation π ℰ) :
    Function.Bijective Pres.sectionToQuotientClass :=
  (isoClassEquivOfIso ((SmallEtaleModuleGlueing.modulesPullbackId X).app ℰ)).bijective.comp
    (Pres.liftToQuotientClass_bijective (𝟙 X))

/-- The lift-to-quotient-class correspondence commutes with arbitrary
precomposition. -/
theorem liftToQuotientClass_naturality (Pres : SymmetricPresentation π ℰ)
    {T R : AlgebraicSpace S} (f : T ⟶ X) (σ : Lift π f) (g : R ⟶ T) :
    Pres.liftToQuotientClass (g ≫ f) (σ.precomp g) =
      quotientPointMap f g (Pres.liftToQuotientClass f σ) := sorry

section
variable (Pres : SymmetricPresentation π ℰ)

/-- Every section of a symmetric projective-bundle presentation is a
closed immersion. -/
theorem section_isClosedImmersion (Pres : SymmetricPresentation π ℰ) (σ : Lift π (𝟙 X)) : IsClosedImmersion σ.hom :=
  sorry

end

/-- The base-change section associated to a lift is a closed immersion. -/
theorem baseChangeSection_isClosedImmersion (Pres : SymmetricPresentation π ℰ) {T : AlgebraicSpace S}
    {f : T ⟶ X} (σ : Lift π f) : IsClosedImmersion σ.baseChangeSection := sorry

/-- The local scheme morphism covering the total space is étale. -/
theorem localCoverHom_etale : Etale Pres.localCoverHom := by
  letI : (MorphismProperty.over (X := S)
      (@AlgebraicGeometry.Etale : MorphismProperty Scheme.{u})).IsMultiplicative :=
    inferInstanceAs
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale : MorphismProperty Scheme.{u})
        (Over.forget S)).IsMultiplicative
  letI : (MorphismProperty.over (X := S)
      (@AlgebraicGeometry.Etale : MorphismProperty Scheme.{u})).RespectsIso :=
    inferInstanceAs
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale : MorphismProperty Scheme.{u})
        (Over.forget S)).RespectsIso
  let Q : MorphismProperty ((Over S)ᵒᵖ ⥤ Type u) :=
    (MorphismProperty.over
      (@AlgebraicGeometry.Etale : MorphismProperty Scheme.{u})).presheaf
  letI : Q.IsMultiplicative := by
    dsimp only [Q, MorphismProperty.presheaf]
    infer_instance
  letI := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (MorphismProperty.over (X := S)
      (@AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}))
  have hatlas : Q (homFunctor Pres.atlas.hom) := by
    have h : Q ((𝟙 _) ≫ homFunctor Pres.atlas.hom) :=
      Pres.atlas.prop.of_etale (𝟙 (ofOver Pres.atlas.left).functorOfPoints)
        (MorphismProperty.id_mem Q _)
    exact (congrArg (fun f ↦ Q f) (Category.id_comp (homFunctor Pres.atlas.hom))).mp h
  have hproj : Q (etaleBaseChangeHom π Pres.atlas) :=
    MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback (homFunctor π) (homFunctor Pres.atlas.hom)).flip hatlas
  let e : (ofOver (Over.mk (Pres.localπ ≫ Pres.atlas.left.hom))).functorOfPoints ≅
      (etaleBaseChangeSpace π Pres.atlas).functorOfPoints :=
    ⟨Pres.localIso.inv, Pres.localIso.hom, Pres.localIso.inv_hom_id,
      Pres.localIso.hom_inv_id⟩
  letI : IsIso e.hom := e.isIso_hom
  constructor
  intro U φ hφ
  change Q (φ ≫ (e.hom ≫ etaleBaseChangeHom π Pres.atlas))
  exact MorphismProperty.comp_mem Q φ _ hφ
    (MorphismProperty.comp_mem Q e.hom _ (MorphismProperty.of_isIso Q e.hom) hproj)

/-- The local scheme morphism covering the total space is étale-locally surjective. -/
theorem localCoverHom_locallySurjective :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) Pres.localCoverHom := by
  letI := Pres.atlas_locallySurjective
  have hproj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
      (etaleBaseChangeHom π Pres.atlas) := by
    constructor
    intro U s
    refine (Scheme.etaleTopology.over S).superset_covering ?_
      (Presheaf.imageSieve_mem (Scheme.etaleTopology.over S) Pres.atlas.hom
        ((homFunctor π).app _ s))
    intro V g hg
    rcases hg with ⟨t, ht⟩
    have hpb := ((evaluation ((Over S)ᵒᵖ) (Type u)).obj (Opposite.op V)).map_isPullback
      (IsPullback.of_hasPullback (homFunctor π) (homFunctor Pres.atlas.hom))
    obtain ⟨p, hp, _⟩ := Types.exists_of_isPullback hpb
      (P.functorOfPoints.map g.op s) t
      (by
        change (homFunctor π).app _ (P.functorOfPoints.map g.op s) =
          (homFunctor Pres.atlas.hom).app _ t
        exact (NatTrans.naturality_apply (homFunctor π) g.op s).trans ht.symm)
    exact ⟨p, hp⟩
  let e : (ofOver (Over.mk (Pres.localπ ≫ Pres.atlas.left.hom))).functorOfPoints ≅
      (etaleBaseChangeSpace π Pres.atlas).functorOfPoints :=
    ⟨Pres.localIso.inv, Pres.localIso.hom, Pres.localIso.inv_hom_id,
      Pres.localIso.hom_inv_id⟩
  letI := hproj
  letI : IsIso e.hom := e.isIso_hom
  letI : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) e.hom :=
    Presheaf.isLocallySurjective_of_iso (Scheme.etaleTopology.over S) e.hom
  change Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
    (e.hom ≫ etaleBaseChangeHom π Pres.atlas)
  infer_instance

end SymmetricPresentation

end ProjectiveBundle
end AlgebraicSpace
end AlgebraicGeometry
