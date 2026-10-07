module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.ConormalAtlas
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.Presentation
public import ReasLib.CategoryTheory.Monoidal.Invertible
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Lemma_66_26_3_Glueing
public import stacks_project.Chap66.Proposition_66_32_1_Comparison
public import stacks_project.Chap67.Lemma_67_14_1_Quotient
public import stacks_project.Chap67.Lemma_67_28_12_IdealSheaf
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal
public import stacks_project.Chap71.Lemma_71_16_4_Lift
public import stacks_project.Chap71.Lemma_71_16_4_Quotient

/-!
# Symmetric presentations of projective bundles of algebraic spaces

A symmetric presentation of `π : 𝐏(ℰ) ⟶ X` is an étale-local scheme-level
symmetric presentation of the relative projective bundle of `ℰ`. The tautological
invertible quotient `π^* ℰ ⟶ 𝒪(1)` is stored on the total space and compared with
the scheme tautological quotient along the chart.
-/

@[expose] public section

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

variable {S : Scheme.{u}} {X P : AlgebraicSpace S} {ℰ : X.Modules} [ℰ.IsQuasicoherent]

/-- An étale-local scheme symmetric presentation of a projective bundle `π : 𝐏(ℰ) ⟶ X`. -/
structure SymmetricPresentation (π : P ⟶ X) (ℰ : X.Modules) [ℰ.IsQuasicoherent] where
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
  /-- Restriction of `π^* ℰ` along the local covering recovers the scheme chart module. -/
  localSourceRestrictIso :
    (Modules.restrictToScheme (Over.mk (localπ ≫ atlas.left.hom))).obj
        ((Modules.pullback (localIso.inv ≫ etaleBaseChangeHom π atlas)).obj
          ((Modules.pullback π).obj ℰ)) ≅
      (Scheme.Modules.pullback localπ).obj localℰ
  /-- The chart restriction of `tautologicalHom`, transported by `tautologicalRestrictIso`
  and `localSourceRestrictIso`, is the scheme tautological quotient map. -/
  tautologicalHom_restrict :
    (Modules.restrictToScheme (Over.mk (localπ ≫ atlas.left.hom))).map
          ((Modules.pullback (localIso.inv ≫ etaleBaseChangeHom π atlas)).map
            tautologicalHom) ≫
        tautologicalRestrictIso.hom =
      localSourceRestrictIso.hom ≫ localPresentation.tautologicalMap

namespace SymmetricPresentation

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
    (localSourceRestrictIso :
      (Modules.restrictToScheme (Over.mk (localπ ≫ atlas.left.hom))).obj
          ((Modules.pullback (localIso.inv ≫ etaleBaseChangeHom π atlas)).obj
            ((Modules.pullback π).obj ℰ)) ≅
        (Scheme.Modules.pullback localπ).obj localℰ)
    (tautologicalHom_restrict :
      (Modules.restrictToScheme (Over.mk (localπ ≫ atlas.left.hom))).map
            ((Modules.pullback (localIso.inv ≫ etaleBaseChangeHom π atlas)).map
              tautologicalHom) ≫
          tautologicalRestrictIso.hom =
        localSourceRestrictIso.hom ≫ localPresentation.tautologicalMap) :
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
    localSourceRestrictIso
    tautologicalHom_restrict }

/-- Pullback of invertible quotients of algebraic-space modules. -/
abbrev pullbackQuotient {T R : AlgebraicSpace S} (f : T ⟶ R) {E : R.Modules}
    (q : InvertibleQuotient E) :
    InvertibleQuotient ((Modules.pullback f).obj E) :=
  AlgebraicSpace.InvertibleQuotient.pullback f q

/-- Pullback of an invertible quotient has the pulled-back target and quotient map. -/
theorem pullbackQuotient_hom {T R : AlgebraicSpace S} (f : T ⟶ R) {E : R.Modules}
    (q : InvertibleQuotient E) :
    (pullbackQuotient f q).hom = (Modules.pullback f).map q.hom := sorry

/-- Pullback of invertible quotients descends to compatible-isomorphism classes. -/
abbrev pullbackQuotientClass {T R : AlgebraicSpace S} (f : T ⟶ R) {E : R.Modules} :
    IsoClass E → IsoClass ((Modules.pullback f).obj E) :=
  AlgebraicSpace.InvertibleQuotient.pullbackClass f

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

/-- The canonical tautological quotient morphism. -/
def tautologicalMap : (Modules.pullback π).obj ℰ ⟶ Pres.tautologicalTarget :=
  Pres.tautologicalHom

/-- The tautological quotient is packaged from the stored first twist and quotient map. -/
theorem tautologicalQuotient_spec :
    Pres.tautologicalQuotient.object = Pres.tautologicalTarget ∧
      Pres.tautologicalQuotient.hom = Pres.tautologicalHom := sorry

/-- Restriction of the tautological first twist recovers the scheme tautological target
via the stored comparison iso. -/
def localTautologicalRestrictIso :
    (Modules.restrictToScheme (Over.mk (Pres.localπ ≫ Pres.atlas.left.hom))).obj
        ((Modules.pullback Pres.localCoverHom).obj Pres.tautologicalTarget) ≅
      Pres.localPresentation.tautologicalTarget :=
  Pres.tautologicalRestrictIso

/-- The restriction comparison of the tautological first twist is the stored chart iso. -/
theorem localTautologicalRestrictIso_eq :
    Pres.localTautologicalRestrictIso = Pres.tautologicalRestrictIso := sorry

/-- The source of the tautological quotient, restricted along the local covering, recovers
the scheme chart module via the stored comparison iso. -/
def localSourceRestrict :
    (Modules.restrictToScheme (Over.mk (Pres.localπ ≫ Pres.atlas.left.hom))).obj
        ((Modules.pullback Pres.localCoverHom).obj ((Modules.pullback π).obj ℰ)) ≅
      (Scheme.Modules.pullback Pres.localπ).obj Pres.localℰ :=
  Pres.localSourceRestrictIso

/-- The source restriction comparison is the stored chart iso. -/
theorem localSourceRestrict_eq :
    Pres.localSourceRestrict = Pres.localSourceRestrictIso := sorry

/-- The chart restriction of the tautological quotient morphism recovers the scheme
tautological map after the stored source and target comparisons. -/
theorem tautologicalMap_restrict :
    (Modules.restrictToScheme (Over.mk (Pres.localπ ≫ Pres.atlas.left.hom))).map
          ((Modules.pullback Pres.localCoverHom).map Pres.tautologicalHom) ≫
        Pres.tautologicalRestrictIso.hom =
      Pres.localSourceRestrictIso.hom ≫ Pres.localPresentation.tautologicalMap :=
  Pres.tautologicalHom_restrict

/-- The concrete quotient on a test algebraic space obtained by pulling back the tautological
quotient along a lift and transporting its source through the lift triangle. -/
def liftSourceQuotient {T : AlgebraicSpace S} {f : T ⟶ X} (σ : Lift π f) :
    InvertibleQuotient ((Modules.pullback f).obj ℰ) :=
  precomposeIso (Lift.pullbackSourceIso σ ℰ).symm
    (pullbackQuotient σ.hom Pres.tautologicalQuotient)

/-- The value of the invertible-quotient-class functor at a test morphism. -/
abbrev QuotientPoint (ℰ : X.Modules) {T : AlgebraicSpace S} (f : T ⟶ X) :=
  IsoClass ((Modules.pullback f).obj ℰ)

/-- Pull back an invertible-quotient class along a morphism of test algebraic spaces, with
the canonical comparison identifying successive pullback with pullback along the composite. -/
def quotientPointMap {T R : AlgebraicSpace S} (f : T ⟶ X) (g : R ⟶ T) :
    QuotientPoint ℰ f → QuotientPoint ℰ (g ≫ f) := fun q ↦
  precomposeIsoClass ((Modules.pullbackComp g f).app ℰ).symm (pullbackQuotientClass g q)

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

end SymmetricPresentation

end ProjectiveBundle
end AlgebraicSpace
end AlgebraicGeometry
