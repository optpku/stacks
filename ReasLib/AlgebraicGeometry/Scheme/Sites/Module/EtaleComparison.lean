/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Equivalence
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.SmallCarrierUniverseLift
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.PullbackSections
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.DerivedAdeq.Comparison
public import ReasLib.AlgebraicGeometry.RingedSite.Module.HigherDirectImage
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.RingedSite.Module.UniverseLift

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.StandardTopology
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.AssociatedModule
open CategoryTheory.Functor

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Etale.ModuleComparison

/-- Restriction to the small étale site preserves limits at the lifted carrier universe. -/
instance etaleRestriction_preservesLimits (τ : StandardTopology) (S : Scheme.{u})
    (hτ : τ ≠ .zariski) :
    PreservesLimits ((SiteRestriction.bigToEtale τ S hτ).modulePushforward.{u+1}) := by
  let forgetTarget := SheafOfModules.forget.{u+1} (Small.ringedSite S).structureSheaf ⋙
    PresheafOfModules.toPresheaf.{u+1} (Small.ringedSite S).structureSheaf.obj
  -- Local instance justification (proof-local temporary data): this reflects-limits witness belongs to the proof's locally defined composite forgetTarget, not a new global forgetful API.
  letI : ReflectsLimits forgetTarget := reflectsLimits_of_reflectsIsomorphisms
  -- Local instance justification (proof-local temporary data): the composite-limit witness is used only to reflect the desired preservation statement through forgetTarget.
  letI : PreservesLimits
      ((SiteRestriction.bigToEtale τ S hτ).modulePushforward.{u+1} ⋙ forgetTarget) := by
    change PreservesLimits ((SheafOfModules.forget (Big.ringedSite τ S).structureSheaf ⋙
      PresheafOfModules.toPresheaf (Big.ringedSite τ S).structureSheaf.obj) ⋙
      (whiskeringLeft _ _ AddCommGrpCat.{u+1}).obj (Scheme.Etale.forget S).op)
    infer_instance
  exact preservesLimits_of_reflects_of_preserves _ forgetTarget

/-- The lifted restriction adjoint follows from preservation of limits in the
existing Grothendieck module category, without a new existence assumption. -/
instance etaleRestriction_isRightAdjoint (τ : StandardTopology) (S : Scheme.{u})
    (hτ : τ ≠ .zariski) :
    ((SiteRestriction.bigToEtale τ S hτ).modulePushforward.{u+1}).IsRightAdjoint :=
  isRightAdjoint_of_preservesLimits_of_isCoseparating.{u+1}
    (isCoseparator_coseparator _) _

/-- Realization of a quasi-coherent small-étale module as a scheme module,
using the existing associated-module equivalence. -/
def etaleModuleRealization (S : Scheme.{u})
    (moduleSheaf : RingedSite.ModuleCat.{u} (Small.ringedSite S))
    [moduleSheaf.IsQuasicoherent] : Scheme.QCoh S :=
  (AssociatedModule.smallFunctor .etale S).asEquivalence.inverse.obj
    ⟨moduleSheaf, inferInstanceAs (SheafOfModules.IsQuasicoherent moduleSheaf)⟩

/-- The counit identifies the realized scheme module with the given small-étale module. -/
def etaleModuleRealizationIso (S : Scheme.{u})
    (moduleSheaf : RingedSite.ModuleCat.{u} (Small.ringedSite S))
    [moduleSheaf.IsQuasicoherent] :
    Small.associatedModule S (etaleModuleRealization S moduleSheaf).obj ≅ moduleSheaf :=
  (SheafOfModules.isQuasicoherent (smallStructureSheaf .etale S)).ι.mapIso
    ((AssociatedModule.smallFunctor .etale S).asEquivalence.counitIso.app
      ⟨moduleSheaf, inferInstanceAs (SheafOfModules.IsQuasicoherent moduleSheaf)⟩)

/-- Extension of quasi-coherent small-étale modules to a standard big site. -/
def etaleModuleExtensionFunctor (τ : StandardTopology) (S : Scheme.{u}) :=
  (AssociatedModule.smallFunctor .etale S).asEquivalence.inverse ⋙
    AssociatedModule.bigFunctor τ S

/-- The extension functor is an equivalence, by the two associated-module equivalences. -/
instance etaleModuleExtensionFunctor_isEquivalence
    (τ : StandardTopology) (S : Scheme.{u}) :
    (etaleModuleExtensionFunctor τ S).IsEquivalence :=
  inferInstanceAs
    (((AssociatedModule.smallFunctor .etale S).asEquivalence.inverse ⋙
      AssociatedModule.bigFunctor τ S).IsEquivalence)

/-- The big-site extension of a given quasi-coherent small-étale module. -/
def etaleModuleExtension (τ : StandardTopology) (S : Scheme.{u})
    (moduleSheaf : RingedSite.ModuleCat.{u} (Small.ringedSite S))
    [moduleSheaf.IsQuasicoherent] : RingedSite.ModuleCat.{u} (Big.ringedSite τ S) :=
  ((etaleModuleExtensionFunctor τ S).obj
    ⟨moduleSheaf, inferInstanceAs (SheafOfModules.IsQuasicoherent moduleSheaf)⟩).obj

/-- The extension is the associated module of the canonical scheme realization. -/
theorem etaleModuleExtension_realization (τ : StandardTopology) (S : Scheme.{u})
    (moduleSheaf : RingedSite.ModuleCat.{u} (Small.ringedSite S))
    [moduleSheaf.IsQuasicoherent] :
    etaleModuleExtension τ S moduleSheaf =
      Big.associatedModule τ S (etaleModuleRealization S moduleSheaf).obj := sorry

/-- Restricting the extension to the small étale site is the realization counit. -/
def etaleModuleExtension_restrictionIso (τ : StandardTopology) (S : Scheme.{u})
    (hτ : τ ≠ .zariski)
    (F : RingedSite.ModuleCat.{u} (Small.ringedSite S)) [F.IsQuasicoherent] :
    (SiteRestriction.bigToEtale τ S hτ).modulePushforward.obj
      (etaleModuleExtension τ S F) ≅ F :=
  etaleModuleRealizationIso S F

namespace GeometricSections

/-- Pull scheme-module sections through the actual fiber-product projections. -/
def sectionUnit {S T : Scheme.{u}} (f : T ⟶ S) (F : S.Modules)
    (U : S.Etale) :
    Scheme.Modules.globalSections ((Scheme.Modules.pullback U.hom).obj F) ⟶
      Scheme.Modules.globalSections
        ((Scheme.Modules.pullback (pullback.snd U.hom f)).obj
          ((Scheme.Modules.pullback f).obj F)) :=
  let condition : pullback.fst U.hom f ≫ U.hom = pullback.snd U.hom f ≫ f :=
    pullback.condition
  Scheme.Modules.globalSectionsPullbackComp (pullback.fst U.hom f) U.hom F ≫
    eqToHom (congrArg (fun g ↦ Scheme.Modules.globalSections
      ((Scheme.Modules.pullback g).obj F)) condition) ≫
    Scheme.Modules.globalSectionsMap
      ((Scheme.Modules.pullbackComp (pullback.snd U.hom f) f).inv.app F)

/-- The direct-image comparison induced by those projection maps. -/
def unit {S T : Scheme.{u}} (f : T ⟶ S) (F : S.Modules) [F.IsQuasicoherent] :
    Etale.Small.associatedModule S F ⟶
      (Etale.Small.ringedHom f).modulePushforward.{u}.obj
        (Etale.Small.associatedModule T ((Scheme.Modules.pullback f).obj F)) where
  val := {
    app := fun U ↦
      let A := (Etale.Small.associatedModule S F).val.obj U
      let B := ((Etale.Small.ringedHom f).modulePushforward.{u}.obj
        (Etale.Small.associatedModule T ((Scheme.Modules.pullback f).obj F))).val.obj U
      @ModuleCat.ofHom _ _ (A : Type u) (B : Type u)
        (ModuleCat.isAddCommGroup A) (ModuleCat.isModule A)
        (ModuleCat.isAddCommGroup B) (ModuleCat.isModule B) {
          toFun := (sectionUnit f F U.unop).hom
          map_add' := (sectionUnit f F U.unop).hom.map_add
          map_smul' := sorry }
    naturality := sorry }

/-- The actual small-étale pullback comparison, obtained by adjunction. -/
def comparison {S T : Scheme.{u}} (f : T ⟶ S) (F : S.Modules) [F.IsQuasicoherent] :
    (Etale.Small.ringedHom f).modulePullback.{u}.obj (Etale.Small.associatedModule S F) ⟶
      Etale.Small.associatedModule T ((Scheme.Modules.pullback f).obj F) :=
  ((RingedSite.Hom.modulePullbackPushforwardAdjunction.{u}
    (Etale.Small.ringedHom f)).homEquiv _ _).symm (unit f F)


/-- Pulling back a quasi-coherent associated module gives the associated pullback. -/
instance comparison_isIso {S T : Scheme.{u}} (f : T ⟶ S) (F : S.Modules)
    [F.IsQuasicoherent] : IsIso (comparison f F) := sorry

/-- Realization of the actual small-etale pullback of the original module. -/
def realizationPullbackIso {S T : Scheme.{u}} (f : T ⟶ S)
    (F : RingedSite.ModuleCat.{u} (Small.ringedSite S)) [F.IsQuasicoherent] :
    Small.associatedModule T
      ((Scheme.Modules.pullback f).obj (etaleModuleRealization S F).obj) ≅
        (Small.ringedHom f).modulePullback.{u}.obj F :=
  (asIso (comparison f (etaleModuleRealization S F).obj)).symm ≪≫
    (Small.ringedHom f).modulePullback.{u}.mapIso (etaleModuleRealizationIso S F)

/-- The specified sections comparison evaluates the small-etale pullback isomorphism
at the identity object after the scheme-module identity-pullback comparison. -/
def sectionIso (τ : StandardTopology) (S : Scheme.{u})
    (F : RingedSite.ModuleCat.{u} (Small.ringedSite S)) [F.IsQuasicoherent]
    (U : Over S) :
    (etaleModuleExtension τ S F).val.presheaf.obj (op U) ≅
      ((Small.ringedHom U.hom).modulePullback.{u}.obj F).val.presheaf.obj
        (op (MorphismProperty.Over.mk _ (𝟙 U.left) inferInstance)) :=
  (forget₂ (ModuleCat _) AddCommGrpCat).mapIso
    ((RingedSpace.moduleGlobalSectionsFunctor U.left.toRingedSpace).mapIso
      ((Scheme.Modules.pullbackId U.left).symm.app
        ((Scheme.Modules.pullback U.hom).obj (etaleModuleRealization S F).obj))) ≪≫
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _) ⋙
      (CategoryTheory.evaluation (U.left.Etale)ᵒᵖ AddCommGrpCat).obj
        (op (MorphismProperty.Over.mk _ (𝟙 U.left) inferInstance))).mapIso
        (realizationPullbackIso U.hom F)

/-- The topology-independent geometric sections rule with values on the actual small-etale pullbacks;
restriction is transported through the specified geometric comparison. -/
def presheaf (S : Scheme.{u})
    (F : RingedSite.ModuleCat.{u} (Small.ringedSite S)) [F.IsQuasicoherent] :
    (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := ((Small.ringedHom U.unop.hom).modulePullback.{u}.obj F).val.presheaf.obj
    (op (MorphismProperty.Over.mk _ (𝟙 U.unop.left) inferInstance))
  map {U V} g := (sectionIso .fppf S F U.unop).inv ≫
    (etaleModuleExtension .fppf S F).val.presheaf.map g ≫
      (sectionIso .fppf S F V.unop).hom
  map_id := sorry
  map_comp := sorry

/-- Natural identification of the extension with the actual geometric sections rule. -/
def sectionsIso (τ : StandardTopology) (S : Scheme.{u})
    (F : RingedSite.ModuleCat.{u} (Small.ringedSite S)) [F.IsQuasicoherent] :
  (etaleModuleExtension τ S F).val.presheaf ≅ presheaf S F :=
  NatIso.ofComponents (fun U ↦ sectionIso τ S F U.unop)
    (sorry)

end GeometricSections

/-- The sheaf condition of the geometric sections rule is transported through
the explicit natural comparison, including its restriction maps. -/
theorem etalePullbackSections_isSheaf (τ : StandardTopology) (S : Scheme.{u})
    (F : RingedSite.ModuleCat.{u} (Small.ringedSite S)) [F.IsQuasicoherent] :
    Presheaf.IsSheaf (τ.overTopology S) (GeometricSections.presheaf S F) :=
  (Presheaf.isSheaf_of_iso_iff (GeometricSections.sectionsIso τ S F)).mp
    (etaleModuleExtension τ S F).isSheaf

/-- Sections of the extension are global sections of small-étale pullback,
with the prescribed geometric pullback-sections rule. -/
theorem etaleModuleExtension_sections (τ : StandardTopology) (S : Scheme.{u})
    (moduleSheaf : RingedSite.ModuleCat.{u} (Small.ringedSite S))
    [moduleSheaf.IsQuasicoherent] (overScheme : Over S) :
    IsIsomorphic
      ((etaleModuleExtension τ S moduleSheaf).val.presheaf.obj (op overScheme))
      (((Small.ringedHom overScheme.hom).modulePullback.{u}.obj moduleSheaf).val.presheaf.obj
        (op (MorphismProperty.Over.mk _ (𝟙 overScheme.left) inferInstance))) := sorry

/-- Realization transports the lifted small-étale input to the existing associated-module
carrier lift at the universe used for higher direct images. -/
theorem etaleModuleCarrierLift_realizationIso (S : Scheme.{u})
    (moduleSheaf : RingedSite.ModuleCat.{u} (Small.ringedSite S))
    [moduleSheaf.IsQuasicoherent] :
    IsIsomorphic (RingedSite.Module.carrierLift (Small.ringedSite S) moduleSheaf)
      (smallCarrierUniverseLift .etale S (etaleModuleRealization S moduleSheaf).obj) := sorry

/-- The extension comparison at the carrier universe required by higher direct images,
using the proved lifted restriction adjoint. -/
theorem etaleModuleExtension_carrierLiftIso (τ : StandardTopology) (S : Scheme.{u})
    (nonZariski : τ ≠ .zariski)
    (moduleSheaf : RingedSite.ModuleCat.{u} (Small.ringedSite S))
    [moduleSheaf.IsQuasicoherent] :
    IsIsomorphic
      (RingedSite.Module.carrierLift (Big.ringedSite τ S) (etaleModuleExtension τ S moduleSheaf))
      ((SiteRestriction.bigToEtale τ S nonZariski).modulePullback.{u + 1}.obj
        (RingedSite.Module.carrierLift (Small.ringedSite S) moduleSheaf)) := sorry


/-- The extension of a quasi-coherent small-étale module is isomorphic to its big étale pullback. -/
theorem bigEtale_associatedModule_piIso
    (S : Scheme.{u}) (F : RingedSite.ModuleCat.{u} (Small.ringedSite S))
    [F.IsQuasicoherent] :
    IsIsomorphic
      (etaleModuleExtension .etale S F)
      ((SiteRestriction.bigToEtale .etale S
          (fun h ↦ nomatch h)).modulePullback.{u}.obj
        F) := sorry

/-- The extension of a quasi-coherent small-étale module is isomorphic to its big fppf pullback. -/
theorem bigFppf_associatedModule_aIso
    (S : Scheme.{u}) (F : RingedSite.ModuleCat.{u} (Small.ringedSite S))
    [F.IsQuasicoherent] :
    IsIsomorphic
      (etaleModuleExtension .fppf S F)
      ((SiteRestriction.bigToEtale .fppf S
          (fun h ↦ nomatch h)).modulePullback.{u}.obj
        F) := sorry


/-- The big fppf pullback pushed forward to the big étale site is isomorphic to the big étale pullback. -/
theorem epsilon_pushforward_aPullbackIso
    (S : Scheme.{u}) (F : RingedSite.ModuleCat.{u} (Small.ringedSite S))
    [F.IsQuasicoherent] :
    IsIsomorphic
      ((Big.toFppfHom .etale S).modulePushforward.obj
        ((SiteRestriction.bigToEtale .fppf S
            (fun h ↦ nomatch h)).modulePullback.{u}.obj
          F))
      ((SiteRestriction.bigToEtale .etale S
          (fun h ↦ nomatch h)).modulePullback.{u}.obj
        F) := sorry

/-- The big fppf pullback pushed forward to the small étale site is isomorphic to the original quasi-coherent module. -/
theorem a_pushforward_aPullbackIso
    (S : Scheme.{u}) (F : RingedSite.ModuleCat.{u} (Small.ringedSite S))
    [F.IsQuasicoherent] :
    IsIsomorphic
      ((SiteRestriction.bigToEtale .fppf S
          (fun h ↦ nomatch h)).modulePushforward.obj
        ((SiteRestriction.bigToEtale .fppf S
            (fun h ↦ nomatch h)).modulePullback.{u}.obj
          F))
      F := sorry

/-- Positive higher direct images from the big fppf site to the big étale site vanish on the pullback of a quasi-coherent small-étale module. -/
theorem epsilon_higherDirectImage_vanishes
    (S : Scheme.{u}) (F : RingedSite.ModuleCat.{u} (Small.ringedSite S))
    [F.IsQuasicoherent] :
    ∀ i : ℕ, 0 < i →
      IsZero
        (RingedSite.Hom.higherDirectImageModule
          (Big.toFppfHom .etale S)
          ((SiteRestriction.bigToEtale .fppf S
              (fun h ↦ nomatch h)).modulePullback.{u + 1}.obj
            (RingedSite.Module.carrierLift (Small.ringedSite S) F))
          i) := sorry

/-- Positive higher direct images from the big fppf site to the small étale site vanish on the pullback of a quasi-coherent small-étale module. -/
theorem a_higherDirectImage_vanishes
    (S : Scheme.{u}) (F : RingedSite.ModuleCat.{u} (Small.ringedSite S))
    [F.IsQuasicoherent] :
    ∀ i : ℕ, 0 < i →
      IsZero
        (RingedSite.Hom.higherDirectImageModule
          (SiteRestriction.bigToEtale .fppf S
              (fun h ↦ nomatch h))
          ((SiteRestriction.bigToEtale .fppf S
              (fun h ↦ nomatch h)).modulePullback.{u + 1}.obj
            (RingedSite.Module.carrierLift (Small.ringedSite S) F))
          i) := sorry

end AlgebraicGeometry.Scheme.Etale.ModuleComparison
