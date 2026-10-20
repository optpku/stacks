/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Module
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Comparison
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Comparison morphisms for small-étale module restrictions

Cartesian evaluation presents restriction to the small étale site. A morphism
of the total category induces a module comparison by scalar compatibility and
the pullback-pushforward adjunction.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite Limits
open Functor RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The coefficient map from an étale neighborhood to the structure ring of
its selected cartesian lift, induced by the identification of schemes. -/
def restrictRingHom {X : GroupoidsOver S} (x : X.total)
    (W : (X.p.obj x).left.Etale) :
    (Scheme.Etale.Small.structureSheaf (X.p.obj x).left).obj.obj (op W) ⟶
      (etaleStructureSheaf X).obj.obj (op ((smallEtaleEval x).obj W)) :=
  (forget₂ CommRingCat RingCat).map
    (Scheme.Γ.map
      (eqToHom (congrArg Over.left
        (@IsHomLift.domain_eq _ _ _ _ X.p _ _ _ _ (etaleOver x W).hom
          (smallEtaleEval_toBase x W)
          (Chosen.cartesianHom.isHomLift X.p (etaleOver x W).hom ⟨x, rfl⟩)))).op) ≫
    (etaleStructureSheafToPushforward X).inv.app (op ((smallEtaleEval x).obj W))

/-- The structure-ring morphism on the small étale site induced by cartesian evaluation. -/
def restrictRingNatTrans {X : GroupoidsOver S} (x : X.total) :
    (Scheme.Etale.Small.structureSheaf (X.p.obj x).left).obj ⟶
      restrictSmallEtale x (etaleStructureSheaf X).obj where
  app W := restrictRingHom x W.unop
  naturality := sorry

/-- The sheaf of modules obtained by cartesian evaluation and restriction of scalars. -/
def restrictEtale {X : GroupoidsOver S}
    (F : SheafOfModules.{u} (etaleStructureSheaf X)) (x : X.total) :
    SheafOfModules.{u} (Scheme.Etale.Small.structureSheaf (X.p.obj x).left) where
  val := (PresheafOfModules.pushforward (restrictRingNatTrans x)).obj F.val
  isSheaf := sorry

/-- Sections of evaluation restriction are sections at the selected cartesian
lift with scalars restricted along the scheme identification. -/
theorem restrictEtale_obj {X : GroupoidsOver S}
    (F : SheafOfModules.{u} (etaleStructureSheaf X)) (x : X.total)
    (W : (X.p.obj x).left.Etale) :
    (restrictEtale F x).val.obj (op W) =
      (ModuleCat.restrictScalars (restrictRingHom x W).hom).obj
        (F.val.obj (op ((smallEtaleEval x).obj W))) :=
  sorry

set_option maxHeartbeats 1600000 in
/-- Canonical small-étale restriction is isomorphic to cartesian evaluation,
via uniqueness of the localization adjoint and cartesian lifts. -/
def restrictEtaleIso {X : GroupoidsOver S}
    (F : SheafOfModules.{u} (etaleStructureSheaf X)) (x : X.total) :
    (restrictModulesToSmallEtale X x).obj F ≅ restrictEtale F x := by
  let domainIso
      (W : (X.p.obj x).left.Etale) :
      ((LocalizationGeometry.siteEquivalence X x).inverse.obj
        ((Scheme.Etale.forget (X.p.obj x).left).obj W)).left ≅
          (smallEtaleEval x).obj W := by
    let e := LocalizationGeometry.siteEquivalence X x
    let i := (X.p.obj x).iteratedSliceEquiv
    let B := (Scheme.Etale.forget (X.p.obj x).left).obj W
    let A := e.inverse.obj B
    let β : (Over.post X.p).obj A ≅ etaleOver x W :=
      i.fullyFaithfulFunctor.preimageIso
        (e.counitIso.app B ≪≫ (i.counitIso.app B).symm)
    let g := (Over.forget (X.p.obj x)).mapIso β
    exact @IsStronglyCartesian.domainIsoOfBaseIso _ _ _ _ X.p
      _ _ _ _ _ _ _ _ g (Over.w β.hom).symm
      (smallEtaleEval_toBase x W) A.hom
      (Chosen.cartesianHom.isStronglyCartesian X.p (etaleOver x W).hom ⟨x, rfl⟩)
      (FiberedSliceEquivalence.strong X.p A.hom)
  let L := (localizedRestriction (etaleRingedSite X) x).obj F
  let H := (Scheme.SiteRestriction.bigToEtale .etale (X.p.obj x).left
    etale_ne_zariski).modulePushforward.{u}
  let B := H.obj ((LocalizationAdjunction.left X x).obj L)
  let adjIso := H.mapIso ((Adjunction.leftAdjointUniq
    (modulePullbackPushforwardAdjunction (localizationToBigEtale X x))
    (LocalizationAdjunction.adjunction X x)).app L)
  let σ : ∀ W : (X.p.obj x).left.Etaleᵒᵖ,
      B.val.obj W ≃+ (restrictEtale F x).val.obj W := fun W =>
    (F.val.presheaf.mapIso (domainIso W.unop).op).symm.addCommGroupIsoToAddEquiv
  let IsLinear : Prop := ∀ W (r :
      (Scheme.Etale.Small.structureSheaf (X.p.obj x).left).obj.obj W)
      (m : B.val.obj W), σ W (r • m) = r • σ W m
  let component (h : IsLinear) (W : (X.p.obj x).left.Etaleᵒᵖ) :
      B.val.obj W ≅ (restrictEtale F x).val.obj W :=
    ((σ W).toLinearEquiv (h W)).toModuleIso
  have coherence : IsLinear ∧ ∀ (h : IsLinear)
      {V W : (X.p.obj x).left.Etaleᵒᵖ} (f : V ⟶ W),
      B.val.map f ≫ (ModuleCat.restrictScalars
          ((Scheme.Etale.Small.structureSheaf (X.p.obj x).left).obj.map f).hom).map
          (component h W).hom =
        (component h V).hom ≫ (restrictEtale F x).val.map f := by
    sorry
  exact adjIso ≪≫ (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (component coherence.1)
      (fun {V W} f => coherence.2 coherence.1 f))

/-- The coefficient maps of cartesian evaluation commute with the fill-in
of a small-étale base-change square and its structure-sheaf map. -/
theorem restrictRingHom_fillIn {X : GroupoidsOver S} {x y : X.total}
    (φ : x ⟶ y) (V' : (X.p.obj y).left.Etale) :
    ((etaleStructureSheaf X).obj.map (comparisonPushHom φ V').op).hom.comp
        (restrictRingHom y V').hom =
      (restrictRingHom x
          ((Scheme.smallEtalePullback (X.p.map φ).left).obj V')).hom.comp
        ((Scheme.Etale.Small.ringedHom (X.p.map φ).left).structureSheafMap.hom.app
          (op V')).hom :=
  sorry

/-- The push-form comparison on evaluation restrictions has components given
by contravariant application to the cartesian fill-in, with compatible scalars. -/
def moduleComparisonPushforwardOnEvaluation {X : GroupoidsOver S} {x y : X.total}
    (φ : x ⟶ y) (F : SheafOfModules.{u} (etaleStructureSheaf X)) :
    restrictEtale F y ⟶
      ((Scheme.Etale.Small.ringedHom (X.p.map φ).left).modulePushforward.{u}).obj
        (restrictEtale F x) where
  val :=
    { app := fun V' ↦
        let a := (X.p.map φ).left
        let U' := (Scheme.smallEtalePullback a).obj V'.unop
        let αy := (restrictRingHom y V'.unop).hom
        let αx := (restrictRingHom x U').hom
        let φring :=
          ((etaleStructureSheaf X).obj.map (comparisonPushHom φ V'.unop).op).hom
        let aSharp :=
          ((Scheme.Etale.Small.ringedHom a).structureSheafMap.hom.app V').hom
        (ModuleCat.restrictScalars αy).map (F.val.map (comparisonPushHom φ V'.unop).op) ≫
          (ModuleCat.restrictScalarsComp'App αy φring (φring.comp αy) rfl _).inv ≫
            (ModuleCat.restrictScalarsCongr
                (restrictRingHom_fillIn φ V'.unop)).hom.app _ ≫
              (ModuleCat.restrictScalarsComp'App aSharp αx (αx.comp aSharp) rfl _).hom
      naturality := sorry }

/-- The push-form comparison between canonical restrictions is the
cartesian evaluation comparison transported through the restriction isomorphisms. -/
def moduleComparisonPushforward {X : GroupoidsOver S} {x y : X.total}
    (φ : x ⟶ y) (F : SheafOfModules.{u} (etaleStructureSheaf X)) :
    (restrictModulesToSmallEtale X y).obj F ⟶
      ((Scheme.Etale.Small.ringedHom (X.p.map φ).left).modulePushforward.{u}).obj
        ((restrictModulesToSmallEtale X x).obj F) :=
  (restrictEtaleIso F y).hom ≫ moduleComparisonPushforwardOnEvaluation φ F ≫
    ((Scheme.Etale.Small.ringedHom (X.p.map φ).left).modulePushforward.{u}).map
      (restrictEtaleIso F x).inv

/-- Under the restriction identifications, the section map of the push-form
comparison is contravariant application to the cartesian fill-in. -/
theorem moduleComparisonPushforward_app {X : GroupoidsOver S} {x y : X.total}
    (φ : x ⟶ y) (F : SheafOfModules.{u} (etaleStructureSheaf X))
    (V' : (X.p.obj y).left.Etale)
    (m : ((restrictModulesToSmallEtale X y).obj F).val.obj (op V')) :
    ((moduleComparisonPushforward φ F ≫
        ((Scheme.Etale.Small.ringedHom (X.p.map φ).left).modulePushforward.{u}).map
          (restrictEtaleIso F x).hom).val.app (op V')) m =
      (F.val.map (comparisonPushHom φ V').op).hom
        ((restrictEtaleIso F y).hom.val.app (op V') m) :=
  sorry

/-- A morphism of a groupoid fibration induces the module comparison from
the small-étale pullback of the target restriction to the source restriction. -/
def moduleComparison {X : GroupoidsOver S} {x y : X.total} (φ : x ⟶ y)
    (F : SheafOfModules.{u} (etaleStructureSheaf X)) :
    ((Scheme.Etale.Small.ringedHom (X.p.map φ).left).modulePullback.{u}).obj
        ((restrictModulesToSmallEtale X y).obj F) ⟶
      (restrictModulesToSmallEtale X x).obj F :=
  (modulePullbackHomEquiv (Scheme.Etale.Small.ringedHom (X.p.map φ).left)
      ((restrictModulesToSmallEtale X y).obj F)
      ((restrictModulesToSmallEtale X x).obj F)).symm
    (moduleComparisonPushforward φ F)

/-- The module comparison is the adjunct of the transported cartesian
section comparison under small-étale module pullback and pushforward. -/
theorem moduleComparison_adjunct {X : GroupoidsOver S} {x y : X.total}
    (φ : x ⟶ y) (F : SheafOfModules.{u} (etaleStructureSheaf X)) :
    modulePullbackHomEquiv (Scheme.Etale.Small.ringedHom (X.p.map φ).left)
        ((restrictModulesToSmallEtale X y).obj F)
        ((restrictModulesToSmallEtale X x).obj F)
        (moduleComparison φ F) =
      moduleComparisonPushforward φ F :=
  sorry

end AlgebraicGeometry.GroupoidsOver
