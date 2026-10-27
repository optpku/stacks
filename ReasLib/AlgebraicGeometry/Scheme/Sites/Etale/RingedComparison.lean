/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Restriction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward.Composition
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
public import Mathlib.CategoryTheory.Whiskering

/-!
# Canonical comparisons on small étale ringed sites

Chosen fibre products give identity and composition isomorphisms, rather than
equalities, for the direct and inverse images of module sheaves.
-/

@[expose] public section

set_option backward.privateInPublic true

open CategoryTheory CategoryTheory.Limits Opposite Functor

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.Small


/-- The fibre-product projection gives the forward identity base comparison. -/
private def ringedBaseIdHom (S : Scheme.{u}) (W : S.Etale) :
    (Scheme.smallEtalePullback (𝟙 S)).obj W ⟶ W :=
  MorphismProperty.Over.homMk (pullback.fst W.hom (𝟙 S))
    (pullback.condition.trans (Category.comp_id _))

/-- The diagonal into the identity fibre product gives the inverse base comparison. -/
private def ringedBaseIdInv (S : Scheme.{u}) (W : S.Etale) :
    W ⟶ (Scheme.smallEtalePullback (𝟙 S)).obj W :=
  MorphismProperty.Over.homMk
    (pullback.lift (𝟙 W.left) W.hom
      ((Category.id_comp W.hom).trans (Category.comp_id W.hom).symm))
    (pullback.lift_snd _ _ _)

/-- The identity fibre-product projection and diagonal are mutually inverse
and are natural in the étale chart. -/
private theorem ringedBaseIdIso_laws (S : Scheme.{u}) :
    (∀ W : S.Etale,
      ringedBaseIdHom S W ≫ ringedBaseIdInv S W = 𝟙 _ ∧
        ringedBaseIdInv S W ≫ ringedBaseIdHom S W = 𝟙 _) ∧
      (∀ {W V : S.Etale} (a : W ⟶ V),
        (Scheme.smallEtalePullback (𝟙 S)).map a ≫ ringedBaseIdHom S V =
          ringedBaseIdHom S W ≫ a) := sorry

/-- Base change along the identity scheme morphism is naturally isomorphic to
the identity on the small étale site, through the fibre-product projection. -/
def ringedBaseIdIso (S : Scheme.{u}) :
    Scheme.smallEtalePullback (𝟙 S) ≅ 𝟭 S.Etale :=
  NatIso.ofComponents (fun W ↦
    { hom := ringedBaseIdHom S W
      inv := ringedBaseIdInv S W
      hom_inv_id := ((ringedBaseIdIso_laws S).1 W).1
      inv_hom_id := ((ringedBaseIdIso_laws S).1 W).2 })
    (ringedBaseIdIso_laws S).2

/-- The identity structure map, transported by the identity base comparison,
is the structure map induced by the fibre-product projection. -/
theorem ringedId_coefficients (S : Scheme.{u}) :
    (RingedSite.Hom.id (ringedSite S)).structureSheafMap ≫
        (Functor.sheafPushforwardContinuousNatTrans (ringedBaseIdIso S).hom
          RingCat.{u} S.smallEtaleTopology S.smallEtaleTopology).app (structureSheaf S) =
      (ringedHom (𝟙 S)).structureSheafMap := sorry

/-- The iterated fibre-product structure map, transported by the canonical
base comparison, is the structure map for the composite scheme morphism. -/
theorem ringedComp_coefficients {R S T : Scheme.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    (RingedSite.Hom.comp (ringedHom f) (ringedHom g)).structureSheafMap ≫
        (@Functor.sheafPushforwardContinuousNatTrans _ _ _ _
          (Scheme.smallEtalePullback (f ≫ g))
          (RingedSite.Hom.comp (ringedHom f) (ringedHom g)).base
          (MorphismProperty.Over.pullbackComp (P := @AlgebraicGeometry.Etale)
            (Q := ⊤) f g).hom
          RingCat.{u} inferInstance T.smallEtaleTopology R.smallEtaleTopology
          (Scheme.smallEtalePullback_isContinuous (f ≫ g))
          (RingedSite.Hom.base_isContinuous
            (RingedSite.Hom.comp (ringedHom f) (ringedHom g)))).app (structureSheaf R) =
      (ringedHom (f ≫ g)).structureSheafMap := sorry

/-- Module direct image along the identity scheme morphism is naturally
isomorphic to the identity functor. -/
def modulePushforwardIdIso (S : Scheme.{u}) :
    (ringedHom (𝟙 S)).modulePushforward.{u} ≅
      𝟭 (RingedSite.ModuleCat.{u} (ringedSite S)) :=
  (@SheafOfModules.pushforwardCongr₂ _ _ _ _
    S.smallEtaleTopology S.smallEtaleTopology
    (Scheme.smallEtalePullback (𝟙 S)) (𝟭 S.Etale)
    (structureSheaf S) (structureSheaf S)
    (Scheme.smallEtalePullback_isContinuous (𝟙 S)) inferInstance
    (𝟙 (structureSheaf S)) (ringedHom (𝟙 S)).structureSheafMap
    (ringedBaseIdIso S) (ringedId_coefficients S)).symm ≪≫
      SheafOfModules.pushforwardId (structureSheaf S)

set_option maxHeartbeats 1600000 in
/-- Iterated module direct image is naturally isomorphic to direct image
along the composite scheme morphism. -/
def modulePushforwardCompIso {R S T : Scheme.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    (ringedHom f).modulePushforward.{u} ⋙ (ringedHom g).modulePushforward.{u} ≅
      (ringedHom (f ≫ g)).modulePushforward.{u} :=
  RingedSite.Hom.modulePushforwardCompIso (ringedHom f) (ringedHom g) ≪≫
    @SheafOfModules.pushforwardCongr₂ _ _ _ _
      T.smallEtaleTopology R.smallEtaleTopology
      (Scheme.smallEtalePullback (f ≫ g))
      (RingedSite.Hom.comp (ringedHom f) (ringedHom g)).base
      (structureSheaf T) (structureSheaf R)
      (Scheme.smallEtalePullback_isContinuous (f ≫ g))
      (RingedSite.Hom.base_isContinuous
        (RingedSite.Hom.comp (ringedHom f) (ringedHom g)))
      (RingedSite.Hom.comp (ringedHom f) (ringedHom g)).structureSheafMap
      (ringedHom (f ≫ g)).structureSheafMap
      (MorphismProperty.Over.pullbackComp (P := @AlgebraicGeometry.Etale) (Q := ⊤) f g)
      (ringedComp_coefficients f g)

/-- Module inverse image along the identity is the identity, by uniqueness of
left adjoints to the canonically identified direct-image functors. -/
def modulePullbackIdIso (S : Scheme.{u}) :
    (ringedHom (𝟙 S)).modulePullback.{u} ≅
      𝟭 (RingedSite.ModuleCat.{u} (ringedSite S)) :=
  Adjunction.leftAdjointUniq
    ((RingedSite.Hom.modulePullbackPushforwardAdjunction (ringedHom (𝟙 S))).ofNatIsoRight
      (modulePushforwardIdIso S)) Adjunction.id

/-- Module inverse image along a composite is naturally isomorphic to the
successive inverse images, using the canonical direct-image comparison. -/
def modulePullbackCompIso {R S T : Scheme.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    (ringedHom (f ≫ g)).modulePullback.{u} ≅
      (ringedHom g).modulePullback.{u} ⋙ (ringedHom f).modulePullback.{u} :=
  Adjunction.leftAdjointUniq
    (RingedSite.Hom.modulePullbackPushforwardAdjunction (ringedHom (f ≫ g)))
    (((RingedSite.Hom.modulePullbackPushforwardAdjunction (ringedHom g)).comp
        (RingedSite.Hom.modulePullbackPushforwardAdjunction (ringedHom f))).ofNatIsoRight
      (modulePushforwardCompIso f g))

/-- On sections, the identity direct-image comparison restricts along the
inverse of the fibre-product projection. -/
theorem modulePushforwardIdIso_app (S : Scheme.{u})
    (M : RingedSite.ModuleCat.{u} (ringedSite S)) (W : S.Etaleᵒᵖ)
    (s : ((ringedHom (𝟙 S)).modulePushforward.{u}.obj M).val.obj W) :
    (((modulePushforwardIdIso S).hom.app M).val.app W) s =
      M.val.map ((ringedBaseIdIso S).inv.app W.unop).op s := sorry

/-- On sections, the composite direct-image comparison restricts along the
canonical map from the single fibre product to the iterated fibre product. -/
theorem modulePushforwardCompIso_app {R S T : Scheme.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (M : RingedSite.ModuleCat.{u} (ringedSite R)) (W : T.Etaleᵒᵖ)
    (s : (((ringedHom f).modulePushforward.{u} ⋙
      (ringedHom g).modulePushforward.{u}).obj M).val.obj W) :
    (((modulePushforwardCompIso f g).hom.app M).val.app W) s =
      M.val.map ((MorphismProperty.Over.pullbackComp
        (P := @AlgebraicGeometry.Etale) (Q := ⊤) f g).hom.app W.unop).op s := sorry

/-- The direct-image composition comparisons satisfy associativity, including
the functor associator and transport along scheme-morphism associativity. -/
theorem modulePushforwardCompIso_assoc {R S T U : Scheme.{u}}
    (f : R ⟶ S) (g : S ⟶ T) (h : T ⟶ U) :
    isoWhiskerRight (modulePushforwardCompIso f g) (ringedHom h).modulePushforward.{u} ≪≫
        modulePushforwardCompIso (f ≫ g) h ≪≫
        eqToIso (congrArg (fun k ↦ (ringedHom k).modulePushforward.{u})
          (Category.assoc f g h)) =
      Functor.associator (ringedHom f).modulePushforward.{u}
          (ringedHom g).modulePushforward.{u} (ringedHom h).modulePushforward.{u} ≪≫
        isoWhiskerLeft (ringedHom f).modulePushforward.{u} (modulePushforwardCompIso g h) ≪≫
        modulePushforwardCompIso f (g ≫ h) := sorry

/-- Composition with the identity at the source agrees with the identity
direct-image comparison and the functor left unitor. -/
theorem modulePushforwardCompIso_id_left {R S : Scheme.{u}} (f : R ⟶ S) :
    modulePushforwardCompIso (𝟙 R) f ≪≫
        eqToIso (congrArg (fun k ↦ (ringedHom k).modulePushforward.{u})
          (Category.id_comp f)) =
      isoWhiskerRight (modulePushforwardIdIso R) (ringedHom f).modulePushforward.{u} ≪≫
        Functor.leftUnitor (ringedHom f).modulePushforward.{u} := sorry

/-- Composition with the identity at the target agrees with the identity
direct-image comparison and the functor right unitor. -/
theorem modulePushforwardCompIso_id_right {R S : Scheme.{u}} (f : R ⟶ S) :
    modulePushforwardCompIso f (𝟙 S) ≪≫
        eqToIso (congrArg (fun k ↦ (ringedHom k).modulePushforward.{u})
          (Category.comp_id f)) =
      isoWhiskerLeft (ringedHom f).modulePushforward.{u} (modulePushforwardIdIso S) ≪≫
        Functor.rightUnitor (ringedHom f).modulePushforward.{u} := sorry

end AlgebraicGeometry.Scheme.Etale.Small
