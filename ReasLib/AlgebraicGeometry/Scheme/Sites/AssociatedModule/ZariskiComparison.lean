module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.CoefficientComparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Ambient
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.EtaleComparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.PullbackSections

/-!
# Associated modules and canonical site presentations

The open-range presentation of a scheme module is identified with its
pullback-sections presentation before passing to the small étale site.
-/

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.DerivedQCoh
open AlgebraicGeometry.Scheme.SiteRestriction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AssociatedModule

/-- The exact pushforward from modules on the opens of a scheme to modules on
its canonical small Zariski ringed site. -/
def zariskiModulePushforward (X : Scheme.{u}) :
    X.Modules ⥤ₑ SheafOfModules.{u} (Zariski.Small.structureSheaf X) :=
  (opensToSmallZariskiModulePushforward X).comp
    (smallZariskiToZariskiSmallModulePushforward X)

set_option backward.privateInPublic true in
private def zariskiPresentationForward (X : Scheme.{u}) (F : X.Modules)
    (U : X.smallZariskiSite) :
    ((zariskiModulePushforward X).obj.obj F).val.obj (op U) →
      (sourceSmallZariskiView X F).val.obj (op U) :=
  fun s ↦
    (((@Modules.restrictFunctorIsoPullback _ _ U.hom U.prop).hom.app F).val.app
      (op ⊤))
      ((@Modules.restrictAppIso _ _ U.hom U.prop F ⊤).inv
        (F.presheaf.map
          (eqToHom (@Scheme.Hom.image_top_eq_opensRange _ _ U.hom U.prop)).op s))

set_option backward.privateInPublic true in
private def zariskiPresentationBackward (X : Scheme.{u}) (F : X.Modules)
    (U : X.smallZariskiSite) :
    (sourceSmallZariskiView X F).val.obj (op U) →
      ((zariskiModulePushforward X).obj.obj F).val.obj (op U) :=
  fun s ↦
    F.presheaf.map
      (eqToHom (@Scheme.Hom.image_top_eq_opensRange _ _ U.hom U.prop).symm).op
      ((@Modules.restrictAppIso _ _ U.hom U.prop F ⊤).hom
        (((@Modules.restrictFunctorIsoPullback _ _ U.hom U.prop).inv.app F).val.app
          (op ⊤) s))

set_option backward.privateInPublic true in
private theorem zariskiPresentationMaps_linear (X : Scheme.{u}) (F : X.Modules)
    (U : X.smallZariskiSite) :
    ((∀ s t, zariskiPresentationForward X F U (s + t) =
        zariskiPresentationForward X F U s + zariskiPresentationForward X F U t) ∧
      (∀ (r : (Zariski.Small.structureSheaf X).obj.obj (op U)) s,
        zariskiPresentationForward X F U (r • s) =
        r • zariskiPresentationForward X F U s)) ∧
    ((∀ s t, zariskiPresentationBackward X F U (s + t) =
        zariskiPresentationBackward X F U s + zariskiPresentationBackward X F U t) ∧
      (∀ (r : (Zariski.Small.structureSheaf X).obj.obj (op U)) s,
        zariskiPresentationBackward X F U (r • s) =
        r • zariskiPresentationBackward X F U s)) := sorry

set_option backward.privateInPublic true in
private theorem zariskiPresentationMaps_restriction (X : Scheme.{u}) (F : X.Modules)
    {U V : X.smallZariskiSiteᵒᵖ} (f : U ⟶ V) :
    (∀ s, zariskiPresentationForward X F V.unop
        (((zariskiModulePushforward X).obj.obj F).val.map f s) =
      (sourceSmallZariskiView X F).val.map f
        (zariskiPresentationForward X F U.unop s)) ∧
    (∀ s, zariskiPresentationBackward X F V.unop
        ((sourceSmallZariskiView X F).val.map f s) =
      (((zariskiModulePushforward X).obj.obj F).val.map f)
        (zariskiPresentationBackward X F U.unop s)) := sorry

set_option backward.privateInPublic true in
private theorem zariskiPresentationMaps_inverse (X : Scheme.{u}) (F : X.Modules)
    (U : X.smallZariskiSite) :
    (∀ s, zariskiPresentationBackward X F U (zariskiPresentationForward X F U s) = s) ∧
    (∀ s, zariskiPresentationForward X F U (zariskiPresentationBackward X F U s) = s) :=
  sorry

-- Local declaration justification (metaprogramming implementation): the exposed
-- isomorphism uses private section maps and their proof laws without publishing them.
set_option backward.privateInPublic true in
/-- Open-range sections of a module, with scalars identified by the canonical
global-functions isomorphism, are the global sections of its open pullbacks. -/
def zariskiPresentationIso (X : Scheme.{u}) (F : X.Modules) :
    (zariskiModulePushforward X).obj.obj F ≅ sourceSmallZariskiView X F where
  hom := ⟨{
    app U :=
      let source := ((zariskiModulePushforward X).obj.obj F).val.obj U
      let target := (sourceSmallZariskiView X F).val.obj U
      @ModuleCat.ofHom ((Zariski.Small.structureSheaf X).obj.obj U) _
        source target (ModuleCat.isAddCommGroup source) (ModuleCat.isModule source)
        (ModuleCat.isAddCommGroup target) (ModuleCat.isModule target) {
      toFun := zariskiPresentationForward X F U.unop
      map_add' := (zariskiPresentationMaps_linear X F U.unop).1.1
      map_smul' := (zariskiPresentationMaps_linear X F U.unop).1.2 }
    naturality {_ _} f := by
      ext s
      exact (zariskiPresentationMaps_restriction X F f).1 s }⟩
  inv := ⟨{
    app U :=
      let source := (sourceSmallZariskiView X F).val.obj U
      let target := ((zariskiModulePushforward X).obj.obj F).val.obj U
      @ModuleCat.ofHom ((Zariski.Small.structureSheaf X).obj.obj U) _
        source target (ModuleCat.isAddCommGroup source) (ModuleCat.isModule source)
        (ModuleCat.isAddCommGroup target) (ModuleCat.isModule target) {
      toFun := zariskiPresentationBackward X F U.unop
      map_add' := (zariskiPresentationMaps_linear X F U.unop).2.1
      map_smul' := (zariskiPresentationMaps_linear X F U.unop).2.2 }
    naturality {_ _} f := by
      ext s
      exact (zariskiPresentationMaps_restriction X F f).2 s }⟩
  hom_inv_id := by
    ext U s
    exact (zariskiPresentationMaps_inverse X F U.unop).1 s
  inv_hom_id := by
    ext U s
    exact (zariskiPresentationMaps_inverse X F U.unop).2 s

/-- The open-range and pullback-sections identification commutes with maps of
scheme modules. -/
theorem zariskiPresentationIso_naturality (X : Scheme.{u})
    {F G : X.Modules} (φ : F ⟶ G) :
    (zariskiModulePushforward X).obj.map φ ≫ (zariskiPresentationIso X G).hom =
      (zariskiPresentationIso X F).hom ≫
        (⟨(Modules.pullbackSectionsFunctor X.smallZariskiForget).map φ⟩ :
          sourceSmallZariskiView X F ⟶ sourceSmallZariskiView X G) := sorry

/-- Étale pullback of the canonical Zariski module presentation is the
associated module on the standard small étale site after coefficient transport. -/
def etalePresentationIso (X : Scheme.{u}) (F : Scheme.QCoh X) :
    (etaleModulePresentation X).functor.obj
      ((epsilonModulePullback X).obj.obj ((zariskiModulePushforward X).obj.obj F.obj)) ≅
        (smallModuleFunctor X .etale).obj F := by
  let E : SheafOfModules.{u} (Etale.Small.structureSheaf X) :=
    ⟨Modules.PullbackSections.modulePresheaf (Scheme.Etale.forget X) F.obj,
      StandardSmall.modulePresheafIsSheaf .etale X F.obj⟩
  let P := PresheafOfModules.sheafification (R := Etale.Small.structureSheaf X)
    (𝟙 (Etale.Small.structureSheaf X).obj)
  let e : smallEtaleZariskiPullbackSections X (sourceSmallZariskiView X F.obj) ≅ E.val :=
    eqToIso (smallEtaleZariskiPullbackSections_sourceView X F.obj)
  let a := (epsilonModulePullback X).obj.mapIso (zariskiPresentationIso X F.obj) ≪≫
    smallEtaleZariskiIso X (sourceSmallZariskiView X F.obj) ≪≫
    P.mapIso e ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction.{u} (R := Etale.Small.structureSheaf X)
      (𝟙 (Etale.Small.structureSheaf X).obj)).counit).app E
  refine (etaleModulePresentation X).functor.mapIso a ≪≫ ?_
  refine (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ ↦ ?_) ?_)
  · exact ModuleCat.isoMk (Iso.refl _) (by intros; rfl)
  · intro U V f
    ext s
    rfl

/-- The coefficient-transported étale presentation commutes with morphisms of
quasi-coherent modules. -/
theorem etalePresentationIso_naturality (X : Scheme.{u})
    {F G : Scheme.QCoh X} (φ : F ⟶ G) :
    (etaleModulePresentation X).functor.map
        ((epsilonModulePullback X).obj.map
          ((zariskiModulePushforward X).obj.map φ.hom)) ≫
      (etalePresentationIso X G).hom =
    (etalePresentationIso X F).hom ≫ (smallModuleFunctor X .etale).map φ := sorry

end AlgebraicGeometry.Scheme.AssociatedModule
