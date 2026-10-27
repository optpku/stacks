/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Terminal
public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Simplicial.Cartesian
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Cocontinuous.StructureIso
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings.Iso
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks

/-!
# Hypercovering descent equivalence for modules

If `K` is a hypercovering of the terminal presheaf, then
`a^* : Mod(O_C) ⥤ Mod(O)` is fully faithful with essential image the cartesian
`O`-modules on `((C / K)_total, O)`, and `a_*` is a quasi-inverse.
-/

-- Local declaration justification (metaprogramming implementation): Exposed descent
-- data retain private reconstruction functions and their named Prop-valued laws.
set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Functor
open RingedSite
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe ι u v w

namespace RingedSite.Localization.AtSimplicialSR

open SemiRepresentableFamily
  (OverSite overTopology overSiteDiagram overSiteTotalTopology totalForget overMap
    overSitePrecoverage overMap_isContinuous overIncl)

variable {X : RingedSite.{u, v, w}}
variable [h_eq : HasEqualizers X.carrier] [h_pb : HasPullbacks X.carrier]
include h_eq h_pb
variable (K : HypercoveringOf.Terminal.{ι} X.siteTopology)
variable [UnivLE.{max ι u v, w}]
variable [HasSheafify (overSiteTotalTopology X.siteTopology K.simplicial) (Type w)]
variable [HasWeakSheafify (overSiteTotalTopology X.siteTopology K.simplicial) (Type w)]
variable [∀ n : SimplexCategory,
    HasSheafify (overTopology X.siteTopology (K.simplicial.obj (op n))) (Type w)]
variable [∀ n : SimplexCategory,
    HasWeakSheafify (overTopology X.siteTopology (K.simplicial.obj (op n))) (Type w)]
variable [∀ P : (Grothendieck (overSiteDiagram K.simplicial))ᵒᵖ ⥤ Type w,
    (totalForget K.simplicial).op.HasPointwiseRightKanExtension P]
variable [∀ n : SimplexCategory, ∀ P : (OverSite (K.simplicial.obj (op n)))ᵒᵖ ⥤ Type w,
    (Grothendieck.ι (overSiteDiagram K.simplicial) (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ∀ P : (OverSite (K.simplicial.obj (op n)))ᵒᵖ ⥤ Type w,
      (overMap (K.simplicial.map φ.op)).op.HasPointwiseRightKanExtension P]
variable [(overSiteTotalTopology X.siteTopology K.simplicial).HasSheafCompose
    (CategoryTheory.forget RingCat.{w})]
variable [X.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n : SimplexCategory,
    (overTopology X.siteTopology (K.simplicial.obj (op n))).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
variable [(SheafOfModules.restrictScalars.{w}
    (toAmbient K.simplicial).structureMap).IsRightAdjoint]
variable [∀ n : SimplexCategory,
    (SheafOfModules.restrictScalars.{w}
      (stageIncl K.simplicial n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (stageMap K.simplicial φ).structureMap).IsRightAdjoint]

/-- The adjunction `a^* ⊣ a_*` of module inverse and direct image along the ringed
augmentation of a hypercovering. -/
def moduleAdjunction :
    modulePullback K.simplicial ⊣ modulePushforward K.simplicial :=
  (toAmbient K.simplicial).moduleAdjunction

/-- `moduleAdjunction` is the ringed-topos module adjunction of `toAmbient`. -/
theorem moduleAdjunction_eq :
    moduleAdjunction K = (toAmbient K.simplicial).moduleAdjunction :=
  sorry

/-- Degree-zero projections along the zero-map cover give local inverse-unit functions. -/
private def descentUnitInvFamily (F : SheafOfModules.{w} X.structureSheaf) (U : X.carrier)
    (I : GrothendieckTopology.Cover.Arrow (⟨Presheaf.imageSieve K.zeroMap
      (PUnit.unit : (Presheaf.terminal X.carrier).obj (op U)),
      K.zero_locallySurjective.imageSieve_mem _⟩ : X.siteTopology.Cover U)) :
    ((Sheaf.InternalModule.ToInternal.underlying X.structureSheaf).obj
      ((modulePushforward K.simplicial).obj ((modulePullback K.simplicial).obj F))).obj.obj
        (op U) ⟶
      ((Sheaf.InternalModule.ToInternal.underlying X.structureSheaf).obj F).obj.obj (op I.Y) :=
  let q := (K.simplicial.obj (op ⦋0⦌)).toPresheafObjEquiv (op I.Y)
    (Presheaf.localPreimage K.zeroMap PUnit.unit I.f I.hf)
  let Z : Grothendieck (overSiteDiagram K.simplicial) :=
    ⟨op ⦋0⦌, ⟨q.1, CategoryTheory.Over.mk q.2⟩⟩
  let f := toAmbient K.simplicial
  let H := (Sheaf.InternalModule.ToInternal.underlying (ringSheaf K.simplicial)).obj
    ((modulePullback K.simplicial).obj F)
  let R := (totalForget K.simplicial).op
  let e := @Cocontinuous.structureMapIso (site K.simplicial) X
    (totalForget K.simplicial) (totalForget_isCocontinuous_site K.simplicial)
    inferInstance inferInstance inferInstance inferInstance (Iso.refl _)
  let N := (f.toTopos.moduleInverseImage X.structureSheaf).obj F
  let c := ((Sheaf.InternalModule.ToInternal.underlying
      (f.toTopos.ringInverseImage.obj X.structureSheaf)).mapIso
        (SheafOfModules.ChangeOfRings.extendRestrictUnitIso e N)).symm ≪≫
    (f.toTopos.moduleInverseImageForgetIso X.structureSheaf).app F ≪≫
    (fullyFaithfulSheafToPresheaf
      (overSiteTotalTopology X.siteTopology K.simplicial) (Type w)).preimageIso
        (X := f.toTopos.inverseImage.obj
          ((Sheaf.InternalModule.ToInternal.underlying X.structureSheaf).obj F))
        (Y := ((totalForget K.simplicial).sheafPushforwardContinuous (Type w)
          (overSiteTotalTopology X.siteTopology K.simplicial) X.siteTopology).obj
            ((Sheaf.InternalModule.ToInternal.underlying X.structureSheaf).obj F))
        (isoSheafify (overSiteTotalTopology X.siteTopology K.simplicial)
          ((totalForget K.simplicial).op_comp_isSheaf
            (overSiteTotalTopology X.siteTopology K.simplicial) X.siteTopology
            ((Sheaf.InternalModule.ToInternal.underlying X.structureSheaf).obj F))).symm
  ((ToposHom.ModulePushforward.forgetIso f).hom.app
      ((modulePullback K.simplicial).obj F)).hom.app (op U) ≫
    ((RightExtension.mk _ (R.ranCounit.app H.obj)).coneAt (op U)).π.app
      (StructuredArrow.mk (Y := op Z) I.f.op) ≫ c.hom.hom.app (op Z)

/-- The degree-zero projection functions agree on every overlap of the zero-map cover. -/
private theorem descentUnitInvFamily_compatible
    (F : SheafOfModules.{w} X.structureSheaf) (U : X.carrier) :
    ∀ ⦃I₁ I₂ : GrothendieckTopology.Cover.Arrow (⟨Presheaf.imageSieve K.zeroMap
        (PUnit.unit : (Presheaf.terminal X.carrier).obj (op U)),
        K.zero_locallySurjective.imageSieve_mem _⟩ : X.siteTopology.Cover U)⦄
      (r : I₁.Relation I₂),
      descentUnitInvFamily K F U I₁ ≫
          ((Sheaf.InternalModule.ToInternal.underlying X.structureSheaf).obj F).obj.map r.g₁.op =
        descentUnitInvFamily K F U I₂ ≫
          ((Sheaf.InternalModule.ToInternal.underlying X.structureSheaf).obj F).obj.map r.g₂.op := sorry

/-- Amalgamation of the zero-map projection family reconstructs a section on the base site. -/
private def descentUnitInvSection (F : SheafOfModules.{w} X.structureSheaf)
    (U : X.carrierᵒᵖ) :
    ((Sheaf.InternalModule.ToInternal.underlying X.structureSheaf).obj
      ((modulePushforward K.simplicial).obj ((modulePullback K.simplicial).obj F))).obj.obj U ⟶
        ((Sheaf.InternalModule.ToInternal.underlying X.structureSheaf).obj F).obj.obj U :=
  ((Sheaf.InternalModule.ToInternal.underlying X.structureSheaf).obj F).property.amalgamate
    ⟨Presheaf.imageSieve K.zeroMap
      (PUnit.unit : (Presheaf.terminal X.carrier).obj U),
      K.zero_locallySurjective.imageSieve_mem _⟩
    (descentUnitInvFamily K F U.unop) (descentUnitInvFamily_compatible K F U.unop)

/-- Inverse-unit section functions commute with restriction on the base site. -/
private theorem descentUnitInvSection_naturality
    (F : SheafOfModules.{w} X.structureSheaf) {U V : X.carrierᵒᵖ} (f : U ⟶ V) :
    ((Sheaf.InternalModule.ToInternal.underlying X.structureSheaf).obj
        ((modulePushforward K.simplicial).obj ((modulePullback K.simplicial).obj F))).obj.map f ≫
      descentUnitInvSection K F V =
    descentUnitInvSection K F U ≫
      ((Sheaf.InternalModule.ToInternal.underlying X.structureSheaf).obj F).obj.map f := sorry

/-- The glued inverse-unit functions form a morphism of underlying sheaves. -/
private def descentUnitInvUnderlyingApp (F : SheafOfModules.{w} X.structureSheaf) :
    (Sheaf.InternalModule.ToInternal.underlying X.structureSheaf).obj
      ((modulePushforward K.simplicial).obj ((modulePullback K.simplicial).obj F)) ⟶
        (Sheaf.InternalModule.ToInternal.underlying X.structureSheaf).obj F :=
  ObjectProperty.homMk
    { app := descentUnitInvSection K F
      naturality := fun _ _ f ↦ descentUnitInvSection_naturality K F f }

/-- The glued inverse-unit morphism preserves addition and scalar multiplication. -/
private theorem descentUnitInvApp_linear (F : SheafOfModules.{w} X.structureSheaf) :
    let R := X.structureSheaf
    let M := (modulePushforward K.simplicial).obj ((modulePullback K.simplicial).obj F)
    let α := descentUnitInvUnderlyingApp K F
    (∀ U (x y : M.val.obj U),
      Sheaf.InternalModule.underlyingApp R α U (x + y) =
        Sheaf.InternalModule.underlyingApp R α U x +
          Sheaf.InternalModule.underlyingApp R α U y) ∧
    (∀ U (r : R.obj.obj U) (x : M.val.obj U),
      Sheaf.InternalModule.underlyingApp R α U (r • x) =
        r • Sheaf.InternalModule.underlyingApp R α U x) := sorry

/-- The glued inverse-unit morphism with its module structure retained. -/
private def descentUnitInvApp (F : SheafOfModules.{w} X.structureSheaf) :
    (modulePushforward K.simplicial).obj ((modulePullback K.simplicial).obj F) ⟶ F :=
  Sheaf.InternalModule.homOfUnderlying X.structureSheaf (descentUnitInvUnderlyingApp K F)
    (descentUnitInvApp_linear K F).1 (descentUnitInvApp_linear K F).2

/-- Reconstructed inverse-unit components are natural in module morphisms. -/
private theorem descentUnitInv_naturality {F F' : SheafOfModules.{w} X.structureSheaf}
    (f : F ⟶ F') :
    (modulePushforward K.simplicial).map ((modulePullback K.simplicial).map f) ≫
        descentUnitInvApp K F' = descentUnitInvApp K F ≫ f := sorry

/-- The gluing inverse to the augmentation unit is a natural transformation of module functors. -/
@[no_expose] def descentUnitInv :
    modulePullback K.simplicial ⋙ modulePushforward K.simplicial ⟶
      𝟭 (SheafOfModules.{w} X.structureSheaf) where
  app := descentUnitInvApp K
  naturality := fun _ _ f ↦ descentUnitInv_naturality K f

/-- The reconstructed inverse unit and the actual adjunction unit satisfy both inverse laws. -/
theorem descentUnitInv_spec :
    (moduleAdjunction K).unit ≫ descentUnitInv K = 𝟙 _ ∧
      descentUnitInv K ≫ (moduleAdjunction K).unit = 𝟙 _ := sorry

/-- A local degree-one lift has concrete summand coordinates in its semi-representable family. -/
private def descentCounitLocalPreimage {U : X.carrier}
    (t : (pullback K.zeroMap K.zeroMap).obj (op U)) {V : X.carrier} (f : V ⟶ U)
    (hf : Presheaf.imageSieve K.oneMap t f) :
    Σ i : (K.simplicial.obj (op ⦋1⦌)).I, V ⟶ (K.simplicial.obj (op ⦋1⦌)).obj i :=
  (K.simplicial.obj (op ⦋1⦌)).toPresheafObjEquiv (op V)
    (Presheaf.localPreimage K.oneMap t f hf)

/-- The first endpoint of a local matching lift has the coordinates of the
restricted first matching projection. -/
private theorem descentCounitLocalPreimage_fst {U : X.carrier}
    (t : (pullback K.zeroMap K.zeroMap).obj (op U)) {V : X.carrier} (f : V ⟶ U)
    (hf : Presheaf.imageSieve K.oneMap t f) :
    let q := descentCounitLocalPreimage K t f hf
    (⟨(K.simplicial.δ 0).f q.1, q.2 ≫ (K.simplicial.δ 0).φ q.1⟩ :
      Σ i : (K.simplicial.obj (op ⦋0⦌)).I, V ⟶ (K.simplicial.obj (op ⦋0⦌)).obj i) =
      (K.simplicial.obj (op ⦋0⦌)).toPresheafObjEquiv (op V)
        (((hypercoveringPresheaf K.simplicial).obj (op ⦋0⦌)).map f.op
          ((pullback.fst K.zeroMap K.zeroMap).app (op U) t)) := sorry

/-- The second endpoint of a local matching lift has the coordinates of the
restricted second matching projection. -/
private theorem descentCounitLocalPreimage_snd {U : X.carrier}
    (t : (pullback K.zeroMap K.zeroMap).obj (op U)) {V : X.carrier} (f : V ⟶ U)
    (hf : Presheaf.imageSieve K.oneMap t f) :
    let q := descentCounitLocalPreimage K t f hf
    (⟨(K.simplicial.δ 1).f q.1, q.2 ≫ (K.simplicial.δ 1).φ q.1⟩ :
      Σ i : (K.simplicial.obj (op ⦋0⦌)).I, V ⟶ (K.simplicial.obj (op ⦋0⦌)).obj i) =
      (K.simplicial.obj (op ⦋0⦌)).toPresheafObjEquiv (op V)
        (((hypercoveringPresheaf K.simplicial).obj (op ⦋0⦌)).map f.op
          ((pullback.snd K.zeroMap K.zeroMap).app (op U) t)) := sorry

/-- The `δ 0` endpoint of a restricted fixed matching lift is the prescribed
slice object over its first vertex, including the component and structure arrow. -/
private theorem descentCounitLocalPreimage_fst_obj {U : X.carrier}
    (x y : Σ i : (K.simplicial.obj (op ⦋0⦌)).I,
      U ⟶ (K.simplicial.obj (op ⦋0⦌)).obj i) :
    let t := (pullbackObjIso K.zeroMap K.zeroMap (op U)).inv
      ((Types.pullbackIsoPullback (K.zeroMap.app (op U)) (K.zeroMap.app (op U))).inv
        ⟨⟨(K.simplicial.obj (op ⦋0⦌)).toPresheafObjMk (op U) x.1 x.2,
          (K.simplicial.obj (op ⦋0⦌)).toPresheafObjMk (op U) y.1 y.2⟩,
          @Subsingleton.elim PUnit inferInstance _ _⟩)
    ∀ {V : X.carrier} (f : V ⟶ U) (hf : Presheaf.imageSieve K.oneMap t f)
      {W : X.carrier} (r : W ⟶ V),
    let q := descentCounitLocalPreimage K t f hf
    (overMap (K.simplicial.δ 0)).obj ⟨q.1, CategoryTheory.Over.mk (r ≫ q.2)⟩ =
      (⟨x.1, CategoryTheory.Over.mk ((r ≫ f) ≫ x.2)⟩ :
        OverSite (K.simplicial.obj (op ⦋0⦌))) := sorry

/-- The `δ 1` endpoint of a restricted fixed matching lift is the prescribed
slice object over its second vertex, including the component and structure arrow. -/
private theorem descentCounitLocalPreimage_snd_obj {U : X.carrier}
    (x y : Σ i : (K.simplicial.obj (op ⦋0⦌)).I,
      U ⟶ (K.simplicial.obj (op ⦋0⦌)).obj i) :
    let t := (pullbackObjIso K.zeroMap K.zeroMap (op U)).inv
      ((Types.pullbackIsoPullback (K.zeroMap.app (op U)) (K.zeroMap.app (op U))).inv
        ⟨⟨(K.simplicial.obj (op ⦋0⦌)).toPresheafObjMk (op U) x.1 x.2,
          (K.simplicial.obj (op ⦋0⦌)).toPresheafObjMk (op U) y.1 y.2⟩,
          @Subsingleton.elim PUnit inferInstance _ _⟩)
    ∀ {V : X.carrier} (f : V ⟶ U) (hf : Presheaf.imageSieve K.oneMap t f)
      {W : X.carrier} (r : W ⟶ V),
    let q := descentCounitLocalPreimage K t f hf
    (overMap (K.simplicial.δ 1)).obj ⟨q.1, CategoryTheory.Over.mk (r ≫ q.2)⟩ =
      (⟨y.1, CategoryTheory.Over.mk ((r ≫ f) ≫ y.2)⟩ :
        OverSite (K.simplicial.obj (op ⦋0⦌))) := sorry

/-- Equality of dependent endpoint objects gives their canonical transport isomorphism. -/
private def descentCounitEndpointIso {U : X.carrier}
    (x y : Σ i : (K.simplicial.obj (op ⦋0⦌)).I,
      U ⟶ (K.simplicial.obj (op ⦋0⦌)).obj i) :
    let t := (pullbackObjIso K.zeroMap K.zeroMap (op U)).inv
      ((Types.pullbackIsoPullback (K.zeroMap.app (op U)) (K.zeroMap.app (op U))).inv
        ⟨⟨(K.simplicial.obj (op ⦋0⦌)).toPresheafObjMk (op U) x.1 x.2,
          (K.simplicial.obj (op ⦋0⦌)).toPresheafObjMk (op U) y.1 y.2⟩,
          @Subsingleton.elim PUnit inferInstance _ _⟩)
    ∀ {V : X.carrier} (f : V ⟶ U) (hf : Presheaf.imageSieve K.oneMap t f)
      {W : X.carrier} (r : W ⟶ V),
    let q := descentCounitLocalPreimage K t f hf
    ∀ b : Fin 2,
    (overMap (K.simplicial.δ b)).obj ⟨q.1, CategoryTheory.Over.mk (r ≫ q.2)⟩ ≅
      (⟨(if b = 0 then x else y).1,
        CategoryTheory.Over.mk ((r ≫ f) ≫ (if b = 0 then x else y).2)⟩ :
          OverSite (K.simplicial.obj (op ⦋0⦌))) :=
  fun {_} f hf {_} r b ↦ match b with
  | 0 => eqToIso (descentCounitLocalPreimage_fst_obj K x y f hf r)
  | 1 => eqToIso (descentCounitLocalPreimage_snd_obj K x y f hf r)

/-- Restricting a fixed matching lift commutes with its endpoint transport isomorphism. -/
private theorem descentCounitEndpointIso_restrict {U : X.carrier}
    (x y : Σ i : (K.simplicial.obj (op ⦋0⦌)).I,
      U ⟶ (K.simplicial.obj (op ⦋0⦌)).obj i) :
    let t := (pullbackObjIso K.zeroMap K.zeroMap (op U)).inv
      ((Types.pullbackIsoPullback (K.zeroMap.app (op U)) (K.zeroMap.app (op U))).inv
        ⟨⟨(K.simplicial.obj (op ⦋0⦌)).toPresheafObjMk (op U) x.1 x.2,
          (K.simplicial.obj (op ⦋0⦌)).toPresheafObjMk (op U) y.1 y.2⟩,
          @Subsingleton.elim PUnit inferInstance _ _⟩)
    ∀ {V : X.carrier} (f : V ⟶ U) (hf : Presheaf.imageSieve K.oneMap t f)
      {W : X.carrier} (r : W ⟶ V),
    let q := descentCounitLocalPreimage K t f hf
    ∀ (b : Fin 2) {T : X.carrier} (s : T ⟶ W),
    let e := if b = 0 then x else y
    let qr : (⟨q.1, CategoryTheory.Over.mk ((s ≫ r) ≫ q.2)⟩ :
        OverSite (K.simplicial.obj (op ⦋1⦌))) ⟶
          ⟨q.1, CategoryTheory.Over.mk (r ≫ q.2)⟩ :=
      Sigma.SigmaHom.mk (CategoryTheory.Over.homMk s (Category.assoc s r q.2).symm)
    let pr : (⟨e.1, CategoryTheory.Over.mk (((s ≫ r) ≫ f) ≫ e.2)⟩ :
        OverSite (K.simplicial.obj (op ⦋0⦌))) ⟶
          ⟨e.1, CategoryTheory.Over.mk ((r ≫ f) ≫ e.2)⟩ :=
      Sigma.SigmaHom.mk (CategoryTheory.Over.homMk s
        ((Category.assoc s (r ≫ f) e.2).symm.trans
          (congrArg (fun a ↦ a ≫ e.2) (Category.assoc s r f).symm)))
    (overMap (K.simplicial.δ b)).map qr ≫ (descentCounitEndpointIso K x y f hf r b).hom =
      (descentCounitEndpointIso K x y f hf (s ≫ r) b).hom ≫ pr := sorry

/-- Evaluated Cartesian transitions and their inverses commute with fixed-lift endpoint
transport and restriction, through the canonical sheafification comparison. -/
private theorem descentCounitEndpointIso_transition
    (G : Cartesian K.simplicial) {U : X.carrier}
    (x y : Σ i : (K.simplicial.obj (op ⦋0⦌)).I,
      U ⟶ (K.simplicial.obj (op ⦋0⦌)).obj i) :
    let t := (pullbackObjIso K.zeroMap K.zeroMap (op U)).inv
      ((Types.pullbackIsoPullback (K.zeroMap.app (op U)) (K.zeroMap.app (op U))).inv
        ⟨⟨(K.simplicial.obj (op ⦋0⦌)).toPresheafObjMk (op U) x.1 x.2,
          (K.simplicial.obj (op ⦋0⦌)).toPresheafObjMk (op U) y.1 y.2⟩,
          @Subsingleton.elim PUnit inferInstance _ _⟩)
    ∀ {V : X.carrier} (f : V ⟶ U) (hf : Presheaf.imageSieve K.oneMap t f)
      {W : X.carrier} (r : W ⟶ V),
    let q := descentCounitLocalPreimage K t f hf
    ∀ (b : Fin 2) {T : X.carrier} (s : T ⟶ W),
    let e := if b = 0 then x else y
    let qr : (⟨q.1, CategoryTheory.Over.mk ((s ≫ r) ≫ q.2)⟩ :
        OverSite (K.simplicial.obj (op ⦋1⦌))) ⟶
          ⟨q.1, CategoryTheory.Over.mk (r ≫ q.2)⟩ :=
      Sigma.SigmaHom.mk (CategoryTheory.Over.homMk s (Category.assoc s r q.2).symm)
    let pr : (⟨e.1, CategoryTheory.Over.mk (((s ≫ r) ≫ f) ≫ e.2)⟩ :
        OverSite (K.simplicial.obj (op ⦋0⦌))) ⟶
          ⟨e.1, CategoryTheory.Over.mk ((r ≫ f) ≫ e.2)⟩ :=
      Sigma.SigmaHom.mk (CategoryTheory.Over.homMk s
        ((Category.assoc s (r ≫ f) e.2).symm.trans
          (congrArg (fun a ↦ a ≫ e.2) (Category.assoc s r f).symm)))
    let J₀ := (overSitePrecoverage X.siteTopology K.simplicial (op ⦋0⦌)).toGrothendieck
    let J₁ := (overSitePrecoverage X.siteTopology K.simplicial (op ⦋1⦌)).toGrothendieck
    let u := overMap (K.simplicial.δ b)
    let topEq := fun n : SimplexCategory ↦
      (Coverage.toGrothendieck_toPrecoverage (overTopology X.siteTopology
        (K.simplicial.obj (op n))).toCoverage).trans
        ((Coverage.gi _).l_u_eq (overTopology X.siteTopology (K.simplicial.obj (op n))))
    let hcont : u.IsContinuous J₁ J₀ :=
      Eq.mpr (congrArg₂ (fun T₁ T₀ ↦ u.IsContinuous T₁ T₀) (topEq ⦋1⦌) (topEq ⦋0⦌))
        (overMap_isContinuous X.siteTopology (K.simplicial.δ b))
    let G₀ := (Grothendieck.fiberRestrict (overSiteDiagram K.simplicial)
      (overSitePrecoverage X.siteTopology K.simplicial) (Type w) ⦋0⦌).obj
        ((Sheaf.InternalModule.ToInternal.underlying (ringSheaf K.simplicial)).obj G.obj)
    let G₁ := (Grothendieck.fiberRestrict (overSiteDiagram K.simplicial)
      (overSitePrecoverage X.siteTopology K.simplicial) (Type w) ⦋1⦌).obj
        ((Sheaf.InternalModule.ToInternal.underlying (ringSheaf K.simplicial)).obj G.obj)
    let c := isoSheafify J₁
      (@Functor.op_comp_isSheaf _ _ _ _ u (Type w) _ J₁ J₀ hcont G₀)
    let τ := @asIso _ _ _ _
      (Grothendieck.Sheaf.sheafTransition (overSiteDiagram K.simplicial)
        (overSitePrecoverage X.siteTopology K.simplicial) (Type w) (SimplexCategory.δ b)
          ((Sheaf.InternalModule.ToInternal.underlying (ringSheaf K.simplicial)).obj G.obj))
      (((isCartesian_iff_underlying K.simplicial G.obj).mp G.property).isIso_transition (SimplexCategory.δ b))
    let Q : OverSite (K.simplicial.obj (op ⦋1⦌)) :=
      ⟨q.1, CategoryTheory.Over.mk (r ≫ q.2)⟩
    let Q' : OverSite (K.simplicial.obj (op ⦋1⦌)) :=
      ⟨q.1, CategoryTheory.Over.mk ((s ≫ r) ≫ q.2)⟩
    let eV := descentCounitEndpointIso K x y f hf r b
    let eW := descentCounitEndpointIso K x y f hf (s ≫ r) b
    (G₁.obj.map qr.op ≫ τ.inv.hom.app (op Q') ≫ c.inv.app (op Q') ≫
        G₀.obj.map eW.inv.op =
      τ.inv.hom.app (op Q) ≫ c.inv.app (op Q) ≫ G₀.obj.map eV.inv.op ≫
        G₀.obj.map pr.op) ∧
      (G₀.obj.map pr.op ≫ G₀.obj.map eW.hom.op ≫ c.hom.app (op Q') ≫
          τ.hom.hom.app (op Q') =
        G₀.obj.map eV.hom.op ≫ c.hom.app (op Q) ≫ τ.hom.hom.app (op Q) ≫
          G₁.obj.map qr.op) := sorry

/-- Local degree-one lifts transfer a Cartesian section to a family over a target vertex. -/
private def descentCounitInvFamily (G : Cartesian K.simplicial)
    (Z : Grothendieck (overSiteDiagram K.simplicial))
    (Y : StructuredArrow (op ((totalForget K.simplicial).obj Z))
      (totalForget K.simplicial).op) :
    let X₀ := (overMap (K.simplicial.map
      (SimplexCategory.const ⦋0⦌ Z.base.unop 0).op)).obj Z.fiber
    let Y₀ := (overMap (K.simplicial.map
      (SimplexCategory.const ⦋0⦌ Y.right.unop.base.unop 0).op)).obj Y.right.unop.fiber
    let x : Σ i : (K.simplicial.obj (op ⦋0⦌)).I,
        Y₀.2.left ⟶ (K.simplicial.obj (op ⦋0⦌)).obj i :=
      ⟨X₀.1, Y.hom.unop ≫ X₀.2.hom⟩
    let y : Σ i : (K.simplicial.obj (op ⦋0⦌)).I,
        Y₀.2.left ⟶ (K.simplicial.obj (op ⦋0⦌)).obj i := ⟨Y₀.1, Y₀.2.hom⟩
    let t := (pullbackObjIso K.zeroMap K.zeroMap (op Y₀.2.left)).inv
      ((Types.pullbackIsoPullback (K.zeroMap.app (op Y₀.2.left))
        (K.zeroMap.app (op Y₀.2.left))).inv
          ⟨⟨(K.simplicial.obj (op ⦋0⦌)).toPresheafObjMk (op Y₀.2.left) x.1 x.2,
            (K.simplicial.obj (op ⦋0⦌)).toPresheafObjMk (op Y₀.2.left) y.1 y.2⟩,
              @Subsingleton.elim PUnit inferInstance _ _⟩)
    let S : (X.siteTopology.over ((K.simplicial.obj (op ⦋0⦌)).obj Y₀.1)).Cover Y₀.2 :=
      ⟨(Sieve.overEquiv Y₀.2).symm (Presheaf.imageSieve K.oneMap t),
        X.siteTopology.overEquiv_symm_mem_over Y₀.2 _ (K.one_locallySurjective.imageSieve_mem t)⟩
    let G₀ := (Grothendieck.fiberRestrict (overSiteDiagram K.simplicial)
      (overSitePrecoverage X.siteTopology K.simplicial) (Type w) ⦋0⦌).obj
        ((Sheaf.InternalModule.ToInternal.underlying (ringSheaf K.simplicial)).obj G.obj)
    let P := (overIncl (K.simplicial.obj (op ⦋0⦌)) Y₀.1).op ⋙ G₀.obj
    ∀ I : S.Arrow, ((Sheaf.InternalModule.ToInternal.underlying (ringSheaf K.simplicial)).obj G.obj).obj.obj (op Z) ⟶ P.obj (op I.Y) :=
    let X₀ := (overMap (K.simplicial.map
      (SimplexCategory.const ⦋0⦌ Z.base.unop 0).op)).obj Z.fiber
    let Y₀ := (overMap (K.simplicial.map
      (SimplexCategory.const ⦋0⦌ Y.right.unop.base.unop 0).op)).obj Y.right.unop.fiber
    let x : Σ i : (K.simplicial.obj (op ⦋0⦌)).I,
        Y₀.2.left ⟶ (K.simplicial.obj (op ⦋0⦌)).obj i :=
      ⟨X₀.1, Y.hom.unop ≫ X₀.2.hom⟩
    let y : Σ i : (K.simplicial.obj (op ⦋0⦌)).I,
        Y₀.2.left ⟶ (K.simplicial.obj (op ⦋0⦌)).obj i := ⟨Y₀.1, Y₀.2.hom⟩
    let t := (pullbackObjIso K.zeroMap K.zeroMap (op Y₀.2.left)).inv
      ((Types.pullbackIsoPullback (K.zeroMap.app (op Y₀.2.left))
        (K.zeroMap.app (op Y₀.2.left))).inv
          ⟨⟨(K.simplicial.obj (op ⦋0⦌)).toPresheafObjMk (op Y₀.2.left) x.1 x.2,
            (K.simplicial.obj (op ⦋0⦌)).toPresheafObjMk (op Y₀.2.left) y.1 y.2⟩,
              @Subsingleton.elim PUnit inferInstance _ _⟩)
    let G₀ := (Grothendieck.fiberRestrict (overSiteDiagram K.simplicial)
      (overSitePrecoverage X.siteTopology K.simplicial) (Type w) ⦋0⦌).obj
        ((Sheaf.InternalModule.ToInternal.underlying (ringSheaf K.simplicial)).obj G.obj)
    fun I ↦
    let rawIso := fun {m n : SimplexCategory} (φ : m ⟶ n) ↦
      let Jm := (overSitePrecoverage X.siteTopology K.simplicial (op m)).toGrothendieck
      let Jn := (overSitePrecoverage X.siteTopology K.simplicial (op n)).toGrothendieck
      let u := overMap (K.simplicial.map φ.op)
      let topEq := fun k : SimplexCategory ↦
        (Coverage.toGrothendieck_toPrecoverage
          (overTopology X.siteTopology (K.simplicial.obj (op k))).toCoverage).trans
            ((Coverage.gi _).l_u_eq (overTopology X.siteTopology (K.simplicial.obj (op k))))
      let hcont : u.IsContinuous Jn Jm :=
        Eq.mpr (congrArg₂ (fun Tn Tm ↦ u.IsContinuous Tn Tm) (topEq n) (topEq m))
          (overMap_isContinuous X.siteTopology (K.simplicial.map φ.op))
      let Gm := (Grothendieck.fiberRestrict (overSiteDiagram K.simplicial)
        (overSitePrecoverage X.siteTopology K.simplicial) (Type w) m).obj
          ((Sheaf.InternalModule.ToInternal.underlying (ringSheaf K.simplicial)).obj G.obj)
      let c := isoSheafify Jn
        (@Functor.op_comp_isSheaf _ _ _ _ u (Type w) _ Jn Jm hcont Gm)
      let τ := @asIso _ _ _ _
        (Grothendieck.Sheaf.sheafTransition (overSiteDiagram K.simplicial)
          (overSitePrecoverage X.siteTopology K.simplicial) (Type w) φ
          ((Sheaf.InternalModule.ToInternal.underlying (ringSheaf K.simplicial)).obj G.obj))
        (((isCartesian_iff_underlying K.simplicial G.obj).mp G.property).isIso_transition φ)
      c ≪≫ (sheafToPresheaf Jn (Type w)).mapIso τ
    let q := descentCounitLocalPreimage K t I.f.left I.hf
    let Q : OverSite (K.simplicial.obj (op ⦋1⦌)) :=
      ⟨q.1, CategoryTheory.Over.mk (𝟙 I.Y.left ≫ q.2)⟩
    let e₀ := descentCounitEndpointIso K x y I.f.left I.hf (𝟙 I.Y.left) 0
    let e₁ := descentCounitEndpointIso K x y I.f.left I.hf (𝟙 I.Y.left) 1
    let a : (⟨x.1, CategoryTheory.Over.mk
        ((𝟙 I.Y.left ≫ I.f.left) ≫ x.2)⟩ :
          OverSite (K.simplicial.obj (op ⦋0⦌))) ⟶ X₀ :=
      Sigma.SigmaHom.mk (CategoryTheory.Over.homMk (I.f.left ≫ Y.hom.unop)
        ((Category.assoc I.f.left Y.hom.unop X₀.2.hom).trans
          (congrArg (fun b ↦ b ≫ x.2) (Category.id_comp I.f.left).symm)))
    let eY := (overIncl (K.simplicial.obj (op ⦋0⦌)) Y₀.1).mapIso
      (CategoryTheory.Over.isoMk (f := CategoryTheory.Over.mk
        ((𝟙 I.Y.left ≫ I.f.left) ≫ y.2)) (g := I.Y) (Iso.refl I.Y.left)
          ((Category.id_comp I.Y.hom).trans ((CategoryTheory.Over.w I.f).symm.trans
            (congrArg (fun b ↦ b ≫ y.2) (Category.id_comp I.f.left).symm))))
    (rawIso (SimplexCategory.const ⦋0⦌ Z.base.unop 0)).inv.app (op Z.fiber) ≫
      G₀.obj.map a.op ≫ G₀.obj.map e₀.hom.op ≫
      (rawIso (SimplexCategory.δ 0)).hom.app (op Q) ≫
      (rawIso (SimplexCategory.δ 1)).inv.app (op Q) ≫
      G₀.obj.map e₁.inv.op ≫ G₀.obj.map eY.inv.op

/-- Local Cartesian transfer maps agree on all overlaps of the matching-map cover. -/
private theorem descentCounitInvFamily_compatible (G : Cartesian K.simplicial)
    (Z : Grothendieck (overSiteDiagram K.simplicial))
    (Y : StructuredArrow (op ((totalForget K.simplicial).obj Z))
      (totalForget K.simplicial).op) :
    let X₀ := (overMap (K.simplicial.map
      (SimplexCategory.const ⦋0⦌ Z.base.unop 0).op)).obj Z.fiber
    let Y₀ := (overMap (K.simplicial.map
      (SimplexCategory.const ⦋0⦌ Y.right.unop.base.unop 0).op)).obj Y.right.unop.fiber
    let x : Σ i : (K.simplicial.obj (op ⦋0⦌)).I,
        Y₀.2.left ⟶ (K.simplicial.obj (op ⦋0⦌)).obj i :=
      ⟨X₀.1, Y.hom.unop ≫ X₀.2.hom⟩
    let y : Σ i : (K.simplicial.obj (op ⦋0⦌)).I,
        Y₀.2.left ⟶ (K.simplicial.obj (op ⦋0⦌)).obj i := ⟨Y₀.1, Y₀.2.hom⟩
    let t := (pullbackObjIso K.zeroMap K.zeroMap (op Y₀.2.left)).inv
      ((Types.pullbackIsoPullback (K.zeroMap.app (op Y₀.2.left))
        (K.zeroMap.app (op Y₀.2.left))).inv
          ⟨⟨(K.simplicial.obj (op ⦋0⦌)).toPresheafObjMk (op Y₀.2.left) x.1 x.2,
            (K.simplicial.obj (op ⦋0⦌)).toPresheafObjMk (op Y₀.2.left) y.1 y.2⟩,
              @Subsingleton.elim PUnit inferInstance _ _⟩)
    let S : (X.siteTopology.over ((K.simplicial.obj (op ⦋0⦌)).obj Y₀.1)).Cover Y₀.2 :=
      ⟨(Sieve.overEquiv Y₀.2).symm (Presheaf.imageSieve K.oneMap t),
        X.siteTopology.overEquiv_symm_mem_over Y₀.2 _ (K.one_locallySurjective.imageSieve_mem t)⟩
    let G₀ := (Grothendieck.fiberRestrict (overSiteDiagram K.simplicial)
      (overSitePrecoverage X.siteTopology K.simplicial) (Type w) ⦋0⦌).obj
        ((Sheaf.InternalModule.ToInternal.underlying (ringSheaf K.simplicial)).obj G.obj)
    let P := (overIncl (K.simplicial.obj (op ⦋0⦌)) Y₀.1).op ⋙ G₀.obj
    ∀ ⦃I₁ I₂ : S.Arrow⦄ (r : I₁.Relation I₂),
      descentCounitInvFamily K G Z Y I₁ ≫ P.map r.g₁.op =
        descentCounitInvFamily K G Z Y I₂ ≫ P.map r.g₂.op := sorry

/-- Amalgamating the matching-cover transfers gives a right-extension cone leg. -/
private def descentCounitConeLeg (G : Cartesian K.simplicial)
    (Z : Grothendieck (overSiteDiagram K.simplicial))
    (Y : StructuredArrow (op ((totalForget K.simplicial).obj Z))
      (totalForget K.simplicial).op) :
    ((Sheaf.InternalModule.ToInternal.underlying (ringSheaf K.simplicial)).obj G.obj).obj.obj
        (op Z) ⟶
      ((Sheaf.InternalModule.ToInternal.underlying (ringSheaf K.simplicial)).obj G.obj).obj.obj
        Y.right :=
  let X₀ := (overMap (K.simplicial.map
    (SimplexCategory.const ⦋0⦌ Z.base.unop 0).op)).obj Z.fiber
  let Y₀ := (overMap (K.simplicial.map
    (SimplexCategory.const ⦋0⦌ Y.right.unop.base.unop 0).op)).obj Y.right.unop.fiber
  let x : Σ i : (K.simplicial.obj (op ⦋0⦌)).I,
      Y₀.2.left ⟶ (K.simplicial.obj (op ⦋0⦌)).obj i :=
    ⟨X₀.1, Y.hom.unop ≫ X₀.2.hom⟩
  let y : Σ i : (K.simplicial.obj (op ⦋0⦌)).I,
      Y₀.2.left ⟶ (K.simplicial.obj (op ⦋0⦌)).obj i := ⟨Y₀.1, Y₀.2.hom⟩
  let t := (pullbackObjIso K.zeroMap K.zeroMap (op Y₀.2.left)).inv
    ((Types.pullbackIsoPullback (K.zeroMap.app (op Y₀.2.left))
      (K.zeroMap.app (op Y₀.2.left))).inv
        ⟨⟨(K.simplicial.obj (op ⦋0⦌)).toPresheafObjMk (op Y₀.2.left) x.1 x.2,
          (K.simplicial.obj (op ⦋0⦌)).toPresheafObjMk (op Y₀.2.left) y.1 y.2⟩,
            @Subsingleton.elim PUnit inferInstance _ _⟩)
  let S : (X.siteTopology.over ((K.simplicial.obj (op ⦋0⦌)).obj Y₀.1)).Cover Y₀.2 :=
    ⟨(Sieve.overEquiv Y₀.2).symm (Presheaf.imageSieve K.oneMap t),
      X.siteTopology.overEquiv_symm_mem_over Y₀.2 _ (K.one_locallySurjective.imageSieve_mem t)⟩
  let G₀ := (Grothendieck.fiberRestrict (overSiteDiagram K.simplicial)
    (overSitePrecoverage X.siteTopology K.simplicial) (Type w) ⦋0⦌).obj
      ((Sheaf.InternalModule.ToInternal.underlying (ringSheaf K.simplicial)).obj G.obj)
  let rawIso := fun {m n : SimplexCategory} (φ : m ⟶ n) ↦
    let Jm := (overSitePrecoverage X.siteTopology K.simplicial (op m)).toGrothendieck
    let Jn := (overSitePrecoverage X.siteTopology K.simplicial (op n)).toGrothendieck
    let u := overMap (K.simplicial.map φ.op)
    let topEq := fun k : SimplexCategory ↦
      (Coverage.toGrothendieck_toPrecoverage
        (overTopology X.siteTopology (K.simplicial.obj (op k))).toCoverage).trans
          ((Coverage.gi _).l_u_eq (overTopology X.siteTopology (K.simplicial.obj (op k))))
    let hcont : u.IsContinuous Jn Jm :=
      Eq.mpr (congrArg₂ (fun Tn Tm ↦ u.IsContinuous Tn Tm) (topEq n) (topEq m))
        (overMap_isContinuous X.siteTopology (K.simplicial.map φ.op))
    let Gm := (Grothendieck.fiberRestrict (overSiteDiagram K.simplicial)
      (overSitePrecoverage X.siteTopology K.simplicial) (Type w) m).obj
        ((Sheaf.InternalModule.ToInternal.underlying (ringSheaf K.simplicial)).obj G.obj)
    let c := isoSheafify Jn
      (@Functor.op_comp_isSheaf _ _ _ _ u (Type w) _ Jn Jm hcont Gm)
    let τ := @asIso _ _ _ _
      (Grothendieck.Sheaf.sheafTransition (overSiteDiagram K.simplicial)
        (overSitePrecoverage X.siteTopology K.simplicial) (Type w) φ
          ((Sheaf.InternalModule.ToInternal.underlying (ringSheaf K.simplicial)).obj G.obj))
        (((isCartesian_iff_underlying K.simplicial G.obj).mp G.property).isIso_transition φ)
    c ≪≫ (sheafToPresheaf Jn (Type w)).mapIso τ
  let topEq := (Coverage.toGrothendieck_toPrecoverage
    (overTopology X.siteTopology (K.simplicial.obj (op ⦋0⦌))).toCoverage).trans
      ((Coverage.gi _).l_u_eq (overTopology X.siteTopology (K.simplicial.obj (op ⦋0⦌))))
  let hG₀ := Eq.mp (congrArg (fun T ↦ Presheaf.IsSheaf T G₀.obj) topEq) G₀.property
  let hP := @Functor.op_comp_isSheaf _ _ _ _
    (overIncl (K.simplicial.obj (op ⦋0⦌)) Y₀.1) (Type w) _
    (X.siteTopology.over ((K.simplicial.obj (op ⦋0⦌)).obj Y₀.1))
    (overTopology X.siteTopology (K.simplicial.obj (op ⦋0⦌)))
    (Sigma.incl_isContinuous (fun i ↦ X.siteTopology.over ((K.simplicial.obj (op ⦋0⦌)).obj i)) Y₀.1)
    ⟨G₀.obj, hG₀⟩
  hP.amalgamate S (descentCounitInvFamily K G Z Y)
      (descentCounitInvFamily_compatible K G Z Y) ≫
    (rawIso (SimplexCategory.const ⦋0⦌ Y.right.unop.base.unop 0)).hom.app
      (op Y.right.unop.fiber)

/-- The amalgamated cone legs commute with morphisms in the right-extension indexing category. -/
private theorem descentCounitCone_naturality (G : Cartesian K.simplicial)
    (Z : Grothendieck (overSiteDiagram K.simplicial))
    {Y Y' : StructuredArrow (op ((totalForget K.simplicial).obj Z))
      (totalForget K.simplicial).op} (f : Y ⟶ Y') :
    descentCounitConeLeg K G Z Y' =
      descentCounitConeLeg K G Z Y ≫
        ((Sheaf.InternalModule.ToInternal.underlying (ringSheaf K.simplicial)).obj G.obj).obj.map
          f.right := sorry

/-- The reconstructed transfers form a cone for the pointwise right Kan extension. -/
private def descentCounitCone (G : Cartesian K.simplicial)
    (Z : Grothendieck (overSiteDiagram K.simplicial)) :
    Cone (StructuredArrow.proj (op ((totalForget K.simplicial).obj Z))
      (totalForget K.simplicial).op ⋙
        ((Sheaf.InternalModule.ToInternal.underlying (ringSheaf K.simplicial)).obj G.obj).obj) where
  pt := ((Sheaf.InternalModule.ToInternal.underlying (ringSheaf K.simplicial)).obj G.obj).obj.obj
    (op Z)
  π :=
    { app := descentCounitConeLeg K G Z
      naturality := fun _ _ f ↦ descentCounitCone_naturality K G Z f }

/-- The pointwise right-extension lift reconstructs inverse-counit sections. -/
private def descentCounitInvSection (G : Cartesian K.simplicial)
    (Z : (Grothendieck (overSiteDiagram K.simplicial))ᵒᵖ) :
    ((Sheaf.InternalModule.ToInternal.underlying (ringSheaf K.simplicial)).obj G.obj).obj.obj Z ⟶
      ((Sheaf.InternalModule.ToInternal.underlying (ringSheaf K.simplicial)).obj
        ((modulePullback K.simplicial).obj ((modulePushforward K.simplicial).obj G.obj))).obj.obj Z :=
  let f := toAmbient K.simplicial
  let M := (modulePushforward K.simplicial).obj G.obj
  let H := (Sheaf.InternalModule.ToInternal.underlying (ringSheaf K.simplicial)).obj G.obj
  let R := (totalForget K.simplicial).op
  let e := @Cocontinuous.structureMapIso (site K.simplicial) X
    (totalForget K.simplicial) (totalForget_isCocontinuous_site K.simplicial)
    inferInstance inferInstance inferInstance inferInstance (Iso.refl _)
  let N := (f.toTopos.moduleInverseImage X.structureSheaf).obj M
  let c := ((Sheaf.InternalModule.ToInternal.underlying
      (f.toTopos.ringInverseImage.obj X.structureSheaf)).mapIso
        (SheafOfModules.ChangeOfRings.extendRestrictUnitIso e N)).symm ≪≫
    (f.toTopos.moduleInverseImageForgetIso X.structureSheaf).app M ≪≫
    (fullyFaithfulSheafToPresheaf
      (overSiteTotalTopology X.siteTopology K.simplicial) (Type w)).preimageIso
        (X := f.toTopos.inverseImage.obj
          ((Sheaf.InternalModule.ToInternal.underlying X.structureSheaf).obj M))
        (Y := ((totalForget K.simplicial).sheafPushforwardContinuous (Type w)
          (overSiteTotalTopology X.siteTopology K.simplicial) X.siteTopology).obj
            ((Sheaf.InternalModule.ToInternal.underlying X.structureSheaf).obj M))
        (isoSheafify (overSiteTotalTopology X.siteTopology K.simplicial)
          ((totalForget K.simplicial).op_comp_isSheaf
            (overSiteTotalTopology X.siteTopology K.simplicial) X.siteTopology
            ((Sheaf.InternalModule.ToInternal.underlying X.structureSheaf).obj M))).symm
  ((R.isPointwiseRightKanExtensionRanCounit H.obj
      (op ((totalForget K.simplicial).obj Z.unop))).lift (descentCounitCone K G Z.unop)) ≫
    ((ToposHom.ModulePushforward.forgetIso f).inv.app G.obj).hom.app
      (op ((totalForget K.simplicial).obj Z.unop)) ≫ c.inv.hom.app Z

/-- The reconstructed inverse-counit section functions commute with restriction. -/
private theorem descentCounitInvSection_naturality (G : Cartesian K.simplicial)
    {U V : (Grothendieck (overSiteDiagram K.simplicial))ᵒᵖ} (f : U ⟶ V) :
    ((Sheaf.InternalModule.ToInternal.underlying (ringSheaf K.simplicial)).obj G.obj).obj.map f ≫
        descentCounitInvSection K G V =
      descentCounitInvSection K G U ≫
        ((Sheaf.InternalModule.ToInternal.underlying (ringSheaf K.simplicial)).obj
          ((modulePullback K.simplicial).obj
            ((modulePushforward K.simplicial).obj G.obj))).obj.map f := sorry

/-- The reconstructed inverse-counit functions form a morphism of underlying sheaves. -/
private def descentCounitInvUnderlyingApp (G : Cartesian K.simplicial) :
    (Sheaf.InternalModule.ToInternal.underlying (ringSheaf K.simplicial)).obj G.obj ⟶
      (Sheaf.InternalModule.ToInternal.underlying (ringSheaf K.simplicial)).obj
        ((modulePullback K.simplicial).obj ((modulePushforward K.simplicial).obj G.obj)) :=
  ObjectProperty.homMk
    { app := descentCounitInvSection K G
      naturality := fun _ _ f ↦ descentCounitInvSection_naturality K G f }

/-- The reconstructed inverse-counit morphism preserves addition and scalar multiplication. -/
private theorem descentCounitInvApp_linear (G : Cartesian K.simplicial) :
    let R := ringSheaf K.simplicial
    let M := G.obj
    let α := descentCounitInvUnderlyingApp K G
    (∀ U (x y : M.val.obj U),
      Sheaf.InternalModule.underlyingApp R α U (x + y) =
        Sheaf.InternalModule.underlyingApp R α U x +
          Sheaf.InternalModule.underlyingApp R α U y) ∧
    (∀ U (r : R.obj.obj U) (x : M.val.obj U),
      Sheaf.InternalModule.underlyingApp R α U (r • x) =
        r • Sheaf.InternalModule.underlyingApp R α U x) := sorry

/-- The inverse-counit reconstruction with its module structure retained. -/
private def descentCounitInvApp (G : Cartesian K.simplicial) :
    G.obj ⟶ (modulePullback K.simplicial).obj ((modulePushforward K.simplicial).obj G.obj) :=
  Sheaf.InternalModule.homOfUnderlying (ringSheaf K.simplicial)
    (descentCounitInvUnderlyingApp K G)
    (descentCounitInvApp_linear K G).1 (descentCounitInvApp_linear K G).2

/-- Reconstructed inverse-counit components are natural in cartesian-module morphisms. -/
private theorem descentCounitInv_naturality {G G' : Cartesian K.simplicial} (f : G ⟶ G') :
    f.hom ≫ descentCounitInvApp K G' =
      descentCounitInvApp K G ≫
        (modulePullback K.simplicial).map ((modulePushforward K.simplicial).map f.hom) := sorry

/-- Cartesian reconstruction gives the inverse of the augmentation counit. -/
@[no_expose] def descentCounitInv :
    (cartesianProperty K.simplicial).ι ⟶
      (cartesianProperty K.simplicial).ι ⋙ modulePushforward K.simplicial ⋙
        modulePullback K.simplicial where
  app := descentCounitInvApp K
  naturality := fun _ _ f ↦ descentCounitInv_naturality K f

/-- Reconstruction and the actual counit on cartesian modules satisfy both inverse laws. -/
theorem descentCounitInv_spec :
    whiskerLeft (cartesianProperty K.simplicial).ι (moduleAdjunction K).counit ≫
        descentCounitInv K = 𝟙 _ ∧
      descentCounitInv K ≫
        whiskerLeft (cartesianProperty K.simplicial).ι (moduleAdjunction K).counit = 𝟙 _ := sorry

/-- A morphism preimage is obtained from the actual unit, direct image, and inverse unit. -/
def modulePullback_preimage {F F' : SheafOfModules.{w} X.structureSheaf}
    (f : (modulePullback K.simplicial).obj F ⟶ (modulePullback K.simplicial).obj F') : F ⟶ F' :=
  (moduleAdjunction K).unit.app F ≫ (modulePushforward K.simplicial).map f ≫
    (descentUnitInv K).app F'

/-- The specified morphism preimage is inverse to the pullback action on morphisms. -/
theorem modulePullback_preimage_spec :
    (∀ {F F' : SheafOfModules.{w} X.structureSheaf}
      (f : (modulePullback K.simplicial).obj F ⟶ (modulePullback K.simplicial).obj F'),
      (modulePullback K.simplicial).map (modulePullback_preimage K f) = f) ∧
    (∀ {F F' : SheafOfModules.{w} X.structureSheaf} (f : F ⟶ F'),
      modulePullback_preimage K ((modulePullback K.simplicial).map f) = f) := sorry

/-- Inverse image `a^*` along a hypercovering is full. -/
instance modulePullback_full : (modulePullback K.simplicial).Full :=
  sorry

/-- Inverse image `a^*` along a hypercovering is faithful. -/
instance modulePullback_faithful : (modulePullback K.simplicial).Faithful :=
  sorry

/-- Inverse image `a^*` along a hypercovering is fully faithful. -/
def modulePullback_fullyFaithful : (modulePullback K.simplicial).FullyFaithful :=
  { preimage := modulePullback_preimage K
    map_preimage := (modulePullback_preimage_spec K).1
    preimage_map := (modulePullback_preimage_spec K).2 }

/-- The unit of `a^* ⊣ a_*` is an isomorphism. -/
theorem unit_app_isIso (F : SheafOfModules.{w} X.structureSheaf) :
    IsIso ((moduleAdjunction K).unit.app F) :=
  sorry

/-- The counit of `a^* ⊣ a_*` is an isomorphism precisely on cartesian `O`-modules. -/
theorem counit_app_isIso_iff_isCartesian
    (G : SheafOfModules.{w} (ringSheaf K.simplicial)) :
    IsIso ((moduleAdjunction K).counit.app G) ↔ IsCartesian K.simplicial G :=
  sorry

/-- The counit of `a^* ⊣ a_*` is an isomorphism on a cartesian `O`-module. -/
theorem counit_app_isIso_of_isCartesian
    (G : SheafOfModules.{w} (ringSheaf K.simplicial))
    (h : IsCartesian K.simplicial G) :
    IsIso ((moduleAdjunction K).counit.app G) :=
  sorry

/-- An `O`-module on `((C / K)_total, O)` lies in the essential image of `a^*` if and only
if it is cartesian. -/
theorem mem_essImage_iff_isCartesian
    (G : SheafOfModules.{w} (ringSheaf K.simplicial)) :
    (modulePullback K.simplicial).essImage G ↔ IsCartesian K.simplicial G :=
  sorry

/-- The functor `a^*` corestricted to cartesian `O`-modules. -/
def cartesianFunctor :
    SheafOfModules.{w} X.structureSheaf ⥤ Cartesian K.simplicial :=
  (cartesianProperty K.simplicial).lift (modulePullback K.simplicial)
    fun F ↦ modulePullback_isCartesian K.simplicial F

/-- On objects, `cartesianFunctor` is module pullback along `a`. -/
theorem cartesianFunctor_obj (F : SheafOfModules.{w} X.structureSheaf) :
    ((cartesianFunctor K).obj F).obj = (modulePullback K.simplicial).obj F :=
  sorry

/-- The functor sending a cartesian `O`-module to `a_*` of its underlying module. -/
def cartesianInverse :
    Cartesian K.simplicial ⥤ SheafOfModules.{w} X.structureSheaf :=
  (cartesianProperty K.simplicial).ι ⋙ modulePushforward K.simplicial

/-- On objects, `cartesianInverse` is module pushforward along `a`. -/
theorem cartesianInverse_obj (G : Cartesian K.simplicial) :
    (cartesianInverse K).obj G = (modulePushforward K.simplicial).obj G.obj :=
  sorry

/-- The unit isomorphism `𝟭 ≅ a^* ⋙ a_*` of hypercovering descent for modules. -/
def cartesianUnitIso :
    𝟭 (SheafOfModules.{w} X.structureSheaf) ≅
      cartesianFunctor K ⋙ cartesianInverse K :=
  NatIso.ofComponents
    (fun F ↦
      { hom := (moduleAdjunction K).unit.app F
        inv := (descentUnitInv K).app F
        hom_inv_id := NatTrans.congr_app (descentUnitInv_spec K).1 F
        inv_hom_id := NatTrans.congr_app (descentUnitInv_spec K).2 F })
    sorry

/-- The component of `cartesianUnitIso` at `F` is the adjunction unit. -/
theorem cartesianUnitIso_hom_app (F : SheafOfModules.{w} X.structureSheaf) :
    (cartesianUnitIso K).hom.app F = (moduleAdjunction K).unit.app F :=
  sorry

/-- The counit isomorphism `a_* ⋙ a^* ≅ 𝟭` on cartesian `O`-modules. -/
def cartesianCounitIso :
    cartesianInverse K ⋙ cartesianFunctor K ≅ 𝟭 (Cartesian K.simplicial) :=
  NatIso.ofComponents
    (fun G ↦
      (cartesianProperty K.simplicial).isoMk
        { hom := (moduleAdjunction K).counit.app G.obj
          inv := (descentCounitInv K).app G
          hom_inv_id := NatTrans.congr_app (descentCounitInv_spec K).1 G
          inv_hom_id := NatTrans.congr_app (descentCounitInv_spec K).2 G })
    sorry

/-- The component of `cartesianCounitIso` at `G` is the adjunction counit on the underlying
module. -/
theorem cartesianCounitIso_hom_app_hom (G : Cartesian K.simplicial) :
    ((cartesianCounitIso K).hom.app G).hom =
      (moduleAdjunction K).counit.app G.obj :=
  sorry

/-- If `K` is a hypercovering of the terminal presheaf, then `a^*` implements an equivalence
between `O_C`-modules and cartesian `O`-modules, with quasi-inverse `a_*`. -/
def cartesianEquivalence :
    SheafOfModules.{w} X.structureSheaf ≌ Cartesian K.simplicial :=
  CategoryTheory.Equivalence.mk (cartesianFunctor K) (cartesianInverse K)
    (cartesianUnitIso K) (cartesianCounitIso K)

/-- The forward functor of `cartesianEquivalence` is `a^*` corestricted to cartesian
`O`-modules. -/
theorem cartesianEquivalence_functor :
    (cartesianEquivalence K).functor = cartesianFunctor K :=
  sorry

/-- The inverse functor of `cartesianEquivalence` is `a_*` on cartesian `O`-modules. -/
theorem cartesianEquivalence_inverse :
    (cartesianEquivalence K).inverse = cartesianInverse K :=
  sorry

end RingedSite.Localization.AtSimplicialSR
