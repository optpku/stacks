/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ProjectiveBundle.Presentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InvertibleQuotient.Conormal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.Tensor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.DescentHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.SchemeComparison
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.ConormalAtlas

/-! # Conormal comparison for sections of projective bundles -/

@[expose] public section

-- Public constructions unfold private chart computations without publishing those helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalCategory.isInvertibleObject
open CategoryTheory.InvertibleQuotient
open AlgebraicGeometry.AlgebraicSpace

noncomputable section
universe u

namespace AlgebraicGeometry
namespace AlgebraicSpace
namespace ProjectiveBundle
namespace SymmetricPresentation

variable {S : Scheme.{u}} {X P : AlgebraicSpace S} {ℰ : X.Modules} [ℰ.IsQuasicoherent]
variable {π : P ⟶ X} (Pres : SymmetricPresentation π ℰ)

/-- The conormal sheaf of the closed section in its original projective bundle. -/
def sectionConormalSheaf (σ : Lift π (𝟙 X)) : X.Modules :=
  @Hom.conormalSheaf S _ _ σ.hom
    (@IsImmersion.ofIsClosedImmersion S _ _ σ.hom (Pres.section_isClosedImmersion σ))

/-- The conormal sheaf of the section induced by a lift after base change. -/
def baseChangeConormalSheaf {T : AlgebraicSpace S} {f : T ⟶ X} (σ : Lift π f) :
    T.Modules :=
  @Hom.conormalSheaf S _ _ σ.baseChangeSection
    (@IsImmersion.ofIsClosedImmersion S _ _ σ.baseChangeSection
      (Pres.baseChangeSection_isClosedImmersion σ))

private def explicitSectionIso.{a, b, c, d} {C : Type a} [Category.{b} C]
    {J : GrothendieckTopology C} {O : Sheaf J RingCat.{c}}
    {M N : SheafOfModules.{d} O} (f : M ⟶ N) [IsIso f] : M ≅ N :=
  SheafOfModules.isoOfBijective f (fun V ↦
    ConcreteCategory.bijective_of_isIso
      ((SheafOfModules.forget O ⋙ PresheafOfModules.evaluation O.obj V).map f))

/-- The identity-base-change transport of an invertible quotient representative. -/
def sectionPullbackQuotient (q : InvertibleQuotient ℰ) :
    InvertibleQuotient ((Modules.pullback (𝟙 X)).obj ℰ) :=
  precomposeIso ((SmallEtaleModuleGlueing.modulesPullbackId X).app ℰ) q

/-- The identity-pullback transport of an invertible quotient commutes with the source
isomorphism. -/
theorem sectionPullbackQuotient_comm (q : InvertibleQuotient ℰ) :
    q.hom ≫ (Iso.refl q.object).hom =
      ((SmallEtaleModuleGlueing.modulesPullbackId X).app ℰ).symm.hom ≫
        (sectionPullbackQuotient q).hom := sorry

/-- A quotient representing the class of a section continues to represent its concrete
tautological quotient after the canonical identity-pullback transport. -/
theorem sectionPullbackQuotient_class (σ : Lift π (𝟙 X))
    (q : InvertibleQuotient ℰ)
    (h : IsoClass.mk q = Pres.sectionToQuotientClass σ) :
    IsoClass.mk (sectionPullbackQuotient q) =
      IsoClass.mk (Pres.liftSourceQuotient σ) := sorry

/-- The conormal object of a section quotient is canonically identified with that of its
identity-base-change transport. -/
def sectionPullbackConormalIso (q : InvertibleQuotient ℰ) :
    conormalObject q ≅ conormalObject (sectionPullbackQuotient q) :=
  conormalObjectIso q (sectionPullbackQuotient q)
    ((SmallEtaleModuleGlueing.modulesPullbackId X).app ℰ).symm (Iso.refl _)
    (sectionPullbackQuotient_comm q)

/-- The canonical morphism from a projective bundle to its base change along the identity of
the base. -/
def sectionAmbientMap : P ⟶ pullback π (𝟙 X) :=
  pullback.lift (𝟙 P) π ((Category.id_comp π).trans (Category.comp_id π).symm)

/-- A section and its identity-base-change section form the canonical ambient square. -/
theorem sectionConormalSquare (σ : Lift π (𝟙 X)) :
    CommSq (𝟙 X) σ.hom σ.baseChangeSection (sectionAmbientMap (π := π)) := sorry

/-- The conormal sheaf of the identity-base-change section maps canonically to the conormal
sheaf of the original section. -/
def sectionConormalTransport (σ : Lift π (𝟙 X)) :
    Pres.baseChangeConormalSheaf σ ⟶ Pres.sectionConormalSheaf σ :=
  (SmallEtaleModuleGlueing.modulesPullbackId X).inv.app
      (Pres.baseChangeConormalSheaf σ) ≫
    @Hom.Conormal.map S _ _ _ _ _ _ _ _ (@IsImmersion.ofIsClosedImmersion S _ _ σ.hom (Pres.section_isClosedImmersion σ)) (@IsImmersion.ofIsClosedImmersion S _ _ σ.baseChangeSection (Pres.baseChangeSection_isClosedImmersion σ)) (sectionConormalSquare (π := π) σ)

/-- The canonical isomorphism from the conormal object of a representative to that of the
concrete quotient attached to the same lift. -/
def liftConormalRepresentativeIso {T : AlgebraicSpace S} {f : T ⟶ X} (σ : Lift π f)
    (q : InvertibleQuotient ((Modules.pullback f).obj ℰ))
    (h : IsoClass.mk q = IsoClass.mk (Pres.liftSourceQuotient σ)) :
    conormalObject q ≅ conormalObject (Pres.liftSourceQuotient σ) :=
  conormalObjectIso q (Pres.liftSourceQuotient σ) (Iso.refl _)
    (targetIsoOfMkEq h)
    ((targetIsoOfMkEq_spec h).trans (Category.id_comp _).symm)

/-- The identity lift of the local scheme presentation. -/
private def localIdentityLift :
    AlgebraicGeometry.Scheme.ProjectiveBundle.Lift Pres.localπ Pres.localπ :=
  AlgebraicGeometry.Scheme.ProjectiveBundle.Lift.identity Pres.localπ

/-- The scheme-level kernel-tensor-inverse to conormal-sheaf map of the local identity
lift, obtained from the homogeneous-coordinate atlas of `localPresentation`. -/
private def localIdentityConormalMap :
    CategoryTheory.InvertibleQuotient.conormalObject
      (Pres.localPresentation.liftSourceQuotient Pres.localπ Pres.localIdentityLift) ⟶
    AlgebraicGeometry.Scheme.Hom.conormalSheaf Pres.localIdentityLift.baseChangeSection :=
  @AlgebraicGeometry.Scheme.ProjectiveBundle.SymmetricPresentation.ConormalAtlas.map
    Pres.atlas.left.left Pres.localScheme Pres.localℰ Pres.localℰ_isQuasicoherent
    Pres.localπ Pres.localPresentation
    (@AlgebraicGeometry.Scheme.ProjectiveBundle.SymmetricPresentation.ConormalAtlas.ofPresentation
      Pres.atlas.left.left Pres.localScheme Pres.localℰ Pres.localℰ_isQuasicoherent
      Pres.localπ Pres.localPresentation)
    Pres.localScheme Pres.localπ Pres.localIdentityLift

/-- The local scheme atlas conormal map is an isomorphism. -/
private theorem localIdentityConormalMap_isIso :
    IsIso Pres.localIdentityConormalMap := sorry

/-- The étale chart of the total space, as an object of `Over S`. -/
private abbrev localCoverOver : Over S :=
  Over.mk (Pres.localπ ≫ Pres.atlas.left.hom)

/-- The ambient comparison from the base change along `g ≫ f` to the base change along `f`. -/
def precompAmbientMap {T R : AlgebraicSpace S} {f : T ⟶ X} (σ : Lift π f) (g : R ⟶ T) :
    pullback π (g ≫ f) ⟶ pullback π f :=
  pullback.lift (pullback.fst π (g ≫ f)) (pullback.snd π (g ≫ f) ≫ g)
    ((pullback.condition (f := π) (g := g ≫ f)).trans
      (Category.assoc (pullback.snd π (g ≫ f)) g f).symm)

/-- The local covering morphism is an immersion of the local scheme into the total space,
as a morphism of schemes over `S` after viewing the identity section of the chart. -/
private theorem localIdentitySection_isImmersion :
    AlgebraicGeometry.IsImmersion Pres.localIdentityLift.baseChangeSection :=
  sorry

/-- The ambient scheme of the local identity section, as an object of `Over S`. -/
private def localIdentityAmbientOver : Over S :=
  Over.mk
    (Limits.pullback.fst Pres.localπ Pres.localπ ≫ Pres.localπ ≫ Pres.atlas.left.hom)

/-- The local identity section, as a morphism in `Over S`. -/
private def localIdentitySectionOver : Pres.localCoverOver ⟶ Pres.localIdentityAmbientOver :=
  Over.homMk Pres.localIdentityLift.baseChangeSection sorry

/-- The covering of the diagonal ambient space by the local scheme pullback. -/
private def localIdentityAmbientCover :
    ofOver Pres.localIdentityAmbientOver ⟶ pullback π π :=
  pullback.lift
    (ofOverHomMk (Limits.pullback.fst Pres.localπ Pres.localπ) sorry ≫ Pres.localCoverHom)
    (ofOverHomMk (Limits.pullback.snd Pres.localπ Pres.localπ) sorry ≫ Pres.localCoverHom)
    sorry

/-- The local identity section is a closed immersion of algebraic spaces. -/
private theorem localIdentitySectionOver_isClosedImmersion :
    IsClosedImmersion (ofOverMap Pres.localIdentitySectionOver) :=
  sorry

/-- The square relating the local identity section to the tautological diagonal section. -/
private theorem localIdentityConormalSquare :
    CommSq Pres.localCoverHom (ofOverMap Pres.localIdentitySectionOver)
      (Lift.identity π).baseChangeSection Pres.localIdentityAmbientCover :=
  sorry

/-- The conormal comparison of the local identity square is an isomorphism. -/
private theorem localIdentityConormalMap_square_isIso :
    IsIso (@Hom.Conormal.map S _ _ _ _ _ _ _ _
      (@IsImmersion.ofIsClosedImmersion S _ _ _ Pres.localIdentitySectionOver_isClosedImmersion)
      (@IsImmersion.ofIsClosedImmersion S _ _ (Lift.identity π).baseChangeSection (Pres.baseChangeSection_isClosedImmersion (Lift.identity π))) Pres.localIdentityConormalSquare) :=
  sorry

/-- Restriction of the pulled-back diagonal conormal sheaf compared with the scheme
conormal sheaf of the local identity section, via `Hom.Conormal.map` and
`Hom.Conormal.restrictToSchemeIso`. -/
private def chartConormalSheafIso :
    (Modules.restrictToScheme Pres.localCoverOver).obj
        ((Modules.pullback Pres.localCoverHom).obj
          (Pres.baseChangeConormalSheaf (Lift.identity π))) ≅
      AlgebraicGeometry.Scheme.Hom.conormalSheaf Pres.localIdentityLift.baseChangeSection :=
  (Modules.restrictToScheme Pres.localCoverOver).mapIso
      (@explicitSectionIso _ _ _ _ _ _
        (@Hom.Conormal.map S _ _ _ _ _ _ _ _
          (@IsImmersion.ofIsClosedImmersion S _ _ _
            Pres.localIdentitySectionOver_isClosedImmersion)
          (@IsImmersion.ofIsClosedImmersion S _ _ (Lift.identity π).baseChangeSection
            (Pres.baseChangeSection_isClosedImmersion (Lift.identity π)))
          Pres.localIdentityConormalSquare)
        Pres.localIdentityConormalMap_square_isIso) ≪≫
    @Hom.Conormal.restrictToSchemeIso S _ _ Pres.localIdentitySectionOver
      Pres.localIdentitySection_isImmersion

/-- The restricted pulled-back tautological quotient, as an invertible quotient of scheme
modules on the local covering. -/
private def restrictTautologicalQuotient :
    InvertibleQuotient
      ((Modules.restrictToScheme Pres.localCoverOver).obj
        ((Modules.pullback Pres.localCoverHom).obj ((Modules.pullback π).obj ℰ)) :
        Pres.localScheme.Modules) where
  object :=
    ((Modules.restrictToScheme Pres.localCoverOver).obj
      ((Modules.pullback Pres.localCoverHom).obj Pres.tautologicalTarget) :
      Pres.localScheme.Modules)
  isInvertible :=
    isInvertibleObject.of_iso Pres.tautologicalRestrictIso.symm
      Pres.localPresentation.tautologicalQuotient.isInvertible
  hom :=
    (Modules.restrictToScheme Pres.localCoverOver).map
      ((Modules.pullback Pres.localCoverHom).map Pres.tautologicalHom)
  hom_epi := sorry

private theorem invertibleIsQuasicoherent {T : AlgebraicSpace S} (L : T.Modules)
    [isInvertibleObject L] : L.IsQuasicoherent := inferInstance

private theorem inverseIsQuasicoherent {T : AlgebraicSpace S} (L : T.Modules)
    [isInvertibleObject L] : (inverse L).IsQuasicoherent := inferInstance

private theorem quotientTargetQuasicoherent {T : AlgebraicSpace S} {E : T.Modules}
    (q : InvertibleQuotient E) : q.object.IsQuasicoherent :=
  @invertibleIsQuasicoherent S T q.object q.isInvertible

private theorem quotientInverseQuasicoherent {T : AlgebraicSpace S} {E : T.Modules}
    (q : InvertibleQuotient E) :
    (@isInvertibleObject.inverse _ _ _ q.object q.isInvertible).IsQuasicoherent :=
  @inverseIsQuasicoherent S T q.object q.isInvertible

private theorem chartQuotientKernelQuasicoherent :
    (kernel (AlgebraicSpace.InvertibleQuotient.pullback Pres.localCoverHom
      Pres.tautologicalQuotient).hom).IsQuasicoherent :=
  @Modules.isQuasicoherent_kernel S _ _ _
    (@Modules.RestrictToScheme.pullbackIsQuasicoherent S _ _ Pres.localCoverHom _
      (Modules.RestrictToScheme.pullbackIsQuasicoherent π ℰ))
    (quotientTargetQuasicoherent (AlgebraicSpace.InvertibleQuotient.pullback
      Pres.localCoverHom Pres.tautologicalQuotient)) _

/-- Kernel-tensor comparison after restriction of the pulled-back tautological quotient. -/
private def restrictPullbackQuotientKernelTensor :
    ((Modules.restrictToScheme Pres.localCoverOver).obj
        (kernel (AlgebraicSpace.InvertibleQuotient.pullback Pres.localCoverHom Pres.tautologicalQuotient).hom) ⊗
      (Modules.restrictToScheme Pres.localCoverOver).obj
        (@isInvertibleObject.inverse _ _ _
          (AlgebraicSpace.InvertibleQuotient.pullback Pres.localCoverHom Pres.tautologicalQuotient).object
          (AlgebraicSpace.InvertibleQuotient.pullback Pres.localCoverHom Pres.tautologicalQuotient).isInvertible) :
        Pres.localCoverOver.left.Modules) ⟶
      (kernel ((Modules.restrictToScheme Pres.localCoverOver).map
          (AlgebraicSpace.InvertibleQuotient.pullback Pres.localCoverHom Pres.tautologicalQuotient).hom) ⊗
        @isInvertibleObject.inverse _ _ _
          ((Modules.restrictToScheme Pres.localCoverOver).obj
            (AlgebraicSpace.InvertibleQuotient.pullback Pres.localCoverHom Pres.tautologicalQuotient).object)
          Pres.restrictTautologicalQuotient.isInvertible :
        Pres.localCoverOver.left.Modules) :=
  Modules.restrictKernelComparison
      (AlgebraicSpace.InvertibleQuotient.pullback Pres.localCoverHom Pres.tautologicalQuotient).hom ⊗ₘ
    @Modules.restrictInverseComparison S Pres.localCoverOver
      (AlgebraicSpace.InvertibleQuotient.pullback Pres.localCoverHom Pres.tautologicalQuotient).object
      (AlgebraicSpace.InvertibleQuotient.pullback Pres.localCoverHom Pres.tautologicalQuotient).isInvertible
      Pres.restrictTautologicalQuotient.isInvertible

/-- Restriction of the conormal object of the pulled-back tautological quotient, compared with
the conormal object of the restricted tautological quotient, via kernel and inverse
comparisons. -/
private def restrictPullbackQuotientConormalHom :
    (Modules.restrictToScheme Pres.localCoverOver).obj
        (conormalObject (AlgebraicSpace.InvertibleQuotient.pullback Pres.localCoverHom Pres.tautologicalQuotient)) ⟶
      conormalObject Pres.restrictTautologicalQuotient :=
  @Modules.restrictTensorOplax S Pres.localCoverOver
      (kernel (AlgebraicSpace.InvertibleQuotient.pullback Pres.localCoverHom Pres.tautologicalQuotient).hom)
      (@isInvertibleObject.inverse _ _ _
        (AlgebraicSpace.InvertibleQuotient.pullback Pres.localCoverHom Pres.tautologicalQuotient).object
        (AlgebraicSpace.InvertibleQuotient.pullback Pres.localCoverHom Pres.tautologicalQuotient).isInvertible)
      Pres.chartQuotientKernelQuasicoherent
      (quotientInverseQuasicoherent (AlgebraicSpace.InvertibleQuotient.pullback
        Pres.localCoverHom Pres.tautologicalQuotient)) ≫
    Pres.restrictPullbackQuotientKernelTensor

/-- The restricted kernel-tensor-inverse comparison is an isomorphism. -/
private theorem restrictPullbackQuotientConormalHom_isIso :
    IsIso (restrictPullbackQuotientConormalHom Pres) :=
  sorry

/-- Restriction of the pulled-back tautological conormal object compared with the conormal
object of the restricted tautological quotient. -/
private def restrictPullbackConormalObjectIso :
    ((Modules.restrictToScheme Pres.localCoverOver).obj
        ((Modules.pullback Pres.localCoverHom).obj (conormalObject Pres.tautologicalQuotient)) :
        Pres.localScheme.Modules) ≅
      conormalObject Pres.restrictTautologicalQuotient :=
  (Modules.restrictToScheme Pres.localCoverOver).mapIso
      (@explicitSectionIso _ _ _ _ _ _
        (AlgebraicSpace.InvertibleQuotient.pullbackConormalObjectComparison Pres.localCoverHom Pres.tautologicalQuotient)
        (AlgebraicSpace.InvertibleQuotient.pullbackConormalObjectComparison_isIso Pres.localCoverHom Pres.tautologicalQuotient)) ≪≫
    @explicitSectionIso _ _ _ _ _ _ (restrictPullbackQuotientConormalHom Pres)
      Pres.restrictPullbackQuotientConormalHom_isIso

/-- The restricted tautological quotient, transported by the stored source and target
chart isos, is the scheme tautological quotient. -/
private theorem restrictTautologicalQuotient_comm :
    Pres.restrictTautologicalQuotient.hom ≫ Pres.tautologicalRestrictIso.hom =
      Pres.localSourceRestrictIso.hom ≫ Pres.localPresentation.tautologicalMap :=
  Pres.tautologicalHom_restrict

/-- Conormal object of the restricted tautological quotient compared with the scheme
tautological conormal object. -/
private def restrictTautologicalConormalObjectIso :=
  @conormalObjectIso Pres.localScheme.Modules
    (inferInstance : Category Pres.localScheme.Modules)
    (Scheme.Modules.instMonoidalCategory Pres.localScheme)
    (inferInstance : Limits.HasZeroMorphisms Pres.localScheme.Modules)
    (inferInstance : Limits.HasKernels Pres.localScheme.Modules)
    _ _ Pres.restrictTautologicalQuotient
    Pres.localPresentation.tautologicalQuotient
    Pres.localSourceRestrictIso Pres.tautologicalRestrictIso
    Pres.restrictTautologicalQuotient_comm

/-- The scheme tautological quotient of the local presentation compared with the identity
lift source quotient. -/
private def localIdentityConormalObjectIso :=
  @conormalObjectIso Pres.localScheme.Modules
    (inferInstance : Category Pres.localScheme.Modules)
    (Scheme.Modules.instMonoidalCategory Pres.localScheme)
    (inferInstance : Limits.HasZeroMorphisms Pres.localScheme.Modules)
    (inferInstance : Limits.HasKernels Pres.localScheme.Modules)
    _ _
    Pres.localPresentation.tautologicalQuotient
    (Pres.localPresentation.liftSourceQuotient Pres.localπ Pres.localIdentityLift)
    (Iso.refl _)
    ((Scheme.Modules.pullbackId Pres.localScheme).symm.app
      Pres.localPresentation.tautologicalTarget)
    sorry

/-- Restriction of the pulled-back tautological conormal object compared with the scheme
identity-lift conormal object, as the composite of the pullback/kernel/inverse comparisons
with the stored `tautologicalRestrictIso` and `localSourceRestrictIso`. -/
private def chartRestrictConormalObjectIso :=
  Pres.restrictPullbackConormalObjectIso ≪≫
    Pres.restrictTautologicalConormalObjectIso ≪≫
    Pres.localIdentityConormalObjectIso

/-- The canonical scheme-chart conormal map commutes with the two kernel-pair actions. -/
private theorem tautologicalConormal_overlap :
    let F : QCoh P := ⟨conormalObject Pres.tautologicalQuotient,
      @AlgebraicSpace.InvertibleQuotient.conormalObject_isQuasicoherent S P _
        (Modules.RestrictToScheme.pullbackIsQuasicoherent π ℰ) Pres.tautologicalQuotient⟩
    let G : QCoh P := ⟨Pres.baseChangeConormalSheaf (Lift.identity π),
      @Hom.conormalSheaf_isQuasicoherent S _ _ _
        (@IsImmersion.ofIsClosedImmersion S _ _ (Lift.identity π).baseChangeSection (Pres.baseChangeSection_isClosedImmersion (Lift.identity π)))⟩
    let f : (QCoh.restrictToScheme Pres.localCoverOver).obj
        ((QCoh.pullback Pres.localCoverHom).obj F) ⟶
      (QCoh.restrictToScheme Pres.localCoverOver).obj
        ((QCoh.pullback Pres.localCoverHom).obj G) :=
      ⟨Pres.chartRestrictConormalObjectIso.hom ≫
        Pres.localIdentityConormalMap ≫ Pres.chartConormalSheafIso.inv⟩
    (@Scheme.QCoh.pullback _ _
      (@atlasGroupoid S P Pres.localCoverOver Pres.localCoverHom
        Pres.localCoverHom_etale).t.left).map f ≫
        @QCoh.action S P Pres.localCoverOver Pres.localCoverHom Pres.localCoverHom_etale G =
      @QCoh.action S P Pres.localCoverOver Pres.localCoverHom Pres.localCoverHom_etale F ≫
        (@Scheme.QCoh.pullback _ _
          (@atlasGroupoid S P Pres.localCoverOver Pres.localCoverHom
            Pres.localCoverHom_etale).s.left).map f := sorry

/-- The tautological kernel tensored with the inverse first twist maps to the diagonal
section's conormal sheaf by descending the canonical compatible scheme-chart morphism. -/
def tautologicalConormalToSheaf :
    conormalObject Pres.tautologicalQuotient ⟶
      Pres.baseChangeConormalSheaf (Lift.identity π) :=
  (@QCoh.descHom S P Pres.localCoverOver Pres.localCoverHom
    Pres.localCoverHom_etale Pres.localCoverHom_locallySurjective
    ⟨conormalObject Pres.tautologicalQuotient,
      @AlgebraicSpace.InvertibleQuotient.conormalObject_isQuasicoherent S P _
        (Modules.RestrictToScheme.pullbackIsQuasicoherent π ℰ) Pres.tautologicalQuotient⟩
    ⟨Pres.baseChangeConormalSheaf (Lift.identity π),
      @Hom.conormalSheaf_isQuasicoherent S _ _ _
        (@IsImmersion.ofIsClosedImmersion S _ _ (Lift.identity π).baseChangeSection (Pres.baseChangeSection_isClosedImmersion (Lift.identity π)))⟩
    ⟨Pres.chartRestrictConormalObjectIso.hom ≫
      Pres.localIdentityConormalMap ≫ Pres.chartConormalSheafIso.inv⟩
    Pres.tautologicalConormal_overlap).hom

/-- The tautological conormal comparison restricts to the scheme atlas map after the
constructed chart identifications. -/
theorem tautologicalConormalToSheaf_restrict :
    (Modules.restrictToScheme Pres.localCoverOver).map
          ((Modules.pullback Pres.localCoverHom).map Pres.tautologicalConormalToSheaf) ≫
        Pres.chartConormalSheafIso.hom =
      Pres.chartRestrictConormalObjectIso.hom ≫ Pres.localIdentityConormalMap := sorry

/-- The ambient comparison from a lift's base-changed bundle to the diagonal base change. -/
def liftToIdentityAmbientMap {T : AlgebraicSpace S} {f : T ⟶ X} (σ : Lift π f) :
    pullback π f ⟶ pullback π π :=
  eqToHom (congrArg (fun h ↦ pullback π h) σ.fac.symm) ≫
    precompAmbientMap (Lift.identity π) σ.hom

/-- The square relating a lift to the tautological diagonal section of the projective bundle. -/
theorem liftToIdentitySquare {T : AlgebraicSpace S} {f : T ⟶ X} (σ : Lift π f) :
    CommSq σ.hom σ.baseChangeSection (Lift.identity π).baseChangeSection
      (liftToIdentityAmbientMap σ) := sorry

/-- The source triangle of `liftSourceQuotient` commutes with pullback of the tautological
quotient. -/
theorem liftSourceQuotient_comm {T : AlgebraicSpace S} {f : T ⟶ X} (σ : Lift π f) :
    (Pres.liftSourceQuotient σ).hom ≫ (Iso.refl (Pres.liftSourceQuotient σ).object).hom =
      (Lift.pullbackSourceIso σ ℰ).symm.hom ≫
        (AlgebraicSpace.InvertibleQuotient.pullback σ.hom Pres.tautologicalQuotient).hom := sorry

/-- The canonical comparison from the kernel-tensor-inverse of a lift's tautological quotient
to the conormal sheaf of the induced closed section. -/
def liftConormalToSheaf {T : AlgebraicSpace S} {f : T ⟶ X} (σ : Lift π f) :
    conormalObject (Pres.liftSourceQuotient σ) ⟶ Pres.baseChangeConormalSheaf σ :=
  (conormalObjectIso (Pres.liftSourceQuotient σ)
      (AlgebraicSpace.InvertibleQuotient.pullback σ.hom Pres.tautologicalQuotient)
      (Lift.pullbackSourceIso σ ℰ).symm (Iso.refl _)
      (Pres.liftSourceQuotient_comm σ)).hom ≫
    (@explicitSectionIso _ _ _ _ _ _
      (AlgebraicSpace.InvertibleQuotient.pullbackConormalObjectComparison σ.hom Pres.tautologicalQuotient)
      (AlgebraicSpace.InvertibleQuotient.pullbackConormalObjectComparison_isIso σ.hom Pres.tautologicalQuotient)).inv ≫
    (Modules.pullback σ.hom).map Pres.tautologicalConormalToSheaf ≫
    @Hom.Conormal.map S _ _ _ _ _ _ _ _ (@IsImmersion.ofIsClosedImmersion S _ _ σ.baseChangeSection (Pres.baseChangeSection_isClosedImmersion σ)) (@IsImmersion.ofIsClosedImmersion S _ _ (Lift.identity π).baseChangeSection (Pres.baseChangeSection_isClosedImmersion (Lift.identity π))) (liftToIdentitySquare σ)

/-- The canonical conormal morphism attached to an explicit quotient representative
corresponding to a lift. -/
def liftConormalMap {T : AlgebraicSpace S} {f : T ⟶ X} (σ : Lift π f)
    (q : InvertibleQuotient ((Modules.pullback f).obj ℰ))
    (h : IsoClass.mk q = IsoClass.mk (Pres.liftSourceQuotient σ)) :
    conormalObject q ⟶ Pres.baseChangeConormalSheaf σ :=
  (Pres.liftConormalRepresentativeIso σ q h).hom ≫ Pres.liftConormalToSheaf σ

/-- Precomposition of lifts gives the canonical square between their induced base-change
sections. -/
theorem precompConormalSquare {T R : AlgebraicSpace S} {f : T ⟶ X} (σ : Lift π f) (g : R ⟶ T) :
    CommSq g (σ.precomp g).baseChangeSection σ.baseChangeSection
      (precompAmbientMap σ g) :=
  ⟨(Lift.baseChangeSection_precomp σ g).symm⟩

/-- The canonical morphism of conormal sheaves associated to precomposition of lifts. -/
def precompConormalSheafMap {T R : AlgebraicSpace S} {f : T ⟶ X} (σ : Lift π f) (g : R ⟶ T) :
    (Modules.pullback g).obj (Pres.baseChangeConormalSheaf σ) ⟶
      Pres.baseChangeConormalSheaf (σ.precomp g) :=
  @Hom.Conormal.map S _ _ _ _ _ _ _ _ (@IsImmersion.ofIsClosedImmersion S _ _ (σ.precomp g).baseChangeSection (Pres.baseChangeSection_isClosedImmersion (σ.precomp g))) (@IsImmersion.ofIsClosedImmersion S _ _ σ.baseChangeSection (Pres.baseChangeSection_isClosedImmersion σ)) (precompConormalSquare σ g)

/-- The pulled-back representative, transported to the source determined by the composite
base morphism. -/
def pullbackRepresentative {T R : AlgebraicSpace S} {f : T ⟶ X} (g : R ⟶ T)
    (q : InvertibleQuotient ((Modules.pullback f).obj ℰ)) :
    InvertibleQuotient ((Modules.pullback (g ≫ f)).obj ℰ) :=
  precomposeIso ((Modules.pullbackCompIso g f).app ℰ).symm (AlgebraicSpace.InvertibleQuotient.pullback g q)

/-- The identity-pullback transport of a pulled-back representative commutes with the source
comparison. -/
theorem pullbackRepresentative_comm {T R : AlgebraicSpace S} {f : T ⟶ X} (g : R ⟶ T)
    (q : InvertibleQuotient ((Modules.pullback f).obj ℰ)) :
    (AlgebraicSpace.InvertibleQuotient.pullback g q).hom ≫ (Iso.refl (AlgebraicSpace.InvertibleQuotient.pullback g q).object).hom =
      ((Modules.pullbackCompIso g f).app ℰ).hom ≫ (pullbackRepresentative g q).hom := sorry

/-- Pulling back a representative corresponding to a lift gives a representative corresponding
to the precomposed lift. -/
theorem pullbackRepresentative_class {T R : AlgebraicSpace S} {f : T ⟶ X} (σ : Lift π f)
    (g : R ⟶ T) (q : InvertibleQuotient ((Modules.pullback f).obj ℰ))
    (h : IsoClass.mk q = IsoClass.mk (Pres.liftSourceQuotient σ)) :
    IsoClass.mk (pullbackRepresentative g q) =
      IsoClass.mk (Pres.liftSourceQuotient (σ.precomp g)) := sorry

/-- The source comparison for the conormal object of a representative under arbitrary
precomposition. -/
def liftConormalPullbackComparison {T R : AlgebraicSpace S} {f : T ⟶ X} (g : R ⟶ T)
    (q : InvertibleQuotient ((Modules.pullback f).obj ℰ)) :
    (Modules.pullback g).obj (conormalObject q) ⟶
      conormalObject (pullbackRepresentative g q) :=
  AlgebraicSpace.InvertibleQuotient.pullbackConormalObjectComparison g q ≫
    (conormalObjectIso (AlgebraicSpace.InvertibleQuotient.pullback g q) (pullbackRepresentative g q)
      ((Modules.pullbackCompIso g f).app ℰ) (Iso.refl _)
      (pullbackRepresentative_comm g q)).hom

/-- a quotient representative corresponding to a section has a canonical
conormal morphism whose target is the conormal sheaf of the section in the original
projective bundle. -/
def sectionConormalMap (Pres : SymmetricPresentation π ℰ)
    (σ : Lift π (𝟙 X)) (q : InvertibleQuotient ℰ)
    (h : IsoClass.mk q = Pres.sectionToQuotientClass σ) :
    conormalObject q ⟶ Pres.sectionConormalSheaf σ :=
  (sectionPullbackConormalIso q).hom ≫
    Pres.liftConormalMap σ (sectionPullbackQuotient q)
      (Pres.sectionPullbackQuotient_class σ q h) ≫
    Pres.sectionConormalTransport σ

/-- the canonical conormal morphism of a section is an isomorphism. -/
theorem sectionConormalMap_isIso (Pres : SymmetricPresentation π ℰ)
    (σ : Lift π (𝟙 X)) (q : InvertibleQuotient ℰ)
    (h : IsoClass.mk q = Pres.sectionToQuotientClass σ) :
    IsIso (sectionConormalMap Pres σ q h) := sorry

/-- the explicit conormal morphisms commute with arbitrary base change,
with the pulled-back representative and its class equality constructed canonically. -/
theorem liftConormalMap_precomp (Pres : SymmetricPresentation π ℰ)
    {T R : AlgebraicSpace S} (f : T ⟶ X) (σ : Lift π f) (g : R ⟶ T)
    (q : InvertibleQuotient ((Modules.pullback f).obj ℰ))
    (h : IsoClass.mk q = IsoClass.mk (Pres.liftSourceQuotient σ)) :
    (Modules.pullback g).map (Pres.liftConormalMap σ q h) ≫
        Pres.precompConormalSheafMap σ g =
      liftConormalPullbackComparison g q ≫
        Pres.liftConormalMap (σ.precomp g) (pullbackRepresentative g q)
          (Pres.pullbackRepresentative_class σ g q h) := sorry

end SymmetricPresentation
end ProjectiveBundle
end AlgebraicSpace
end AlgebraicGeometry
