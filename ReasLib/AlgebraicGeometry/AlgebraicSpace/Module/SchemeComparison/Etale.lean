/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.SchemeComparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.RingedComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.RestrictToScheme.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Module
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Small étale modules on represented schemes -/

@[expose] public section

set_option backward.privateInPublic true
set_option maxHeartbeats 1600000

open CategoryTheory Opposite Functor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SchemeEtaleModules

variable {S : Scheme.{u}} (U : Over S)

/-- The structure map of a represented étale chart, recovered by Yoneda. -/
def chartHom (A : smallEtaleSite (ofOver U)) : A.left ⟶ U :=
  ofOverPreimage A.hom

/-- Recovered chart maps are étale, and recovered triangles commute. -/
private theorem siteInverse_laws :
    (∀ A : smallEtaleSite (ofOver U), AlgebraicGeometry.Etale (chartHom U A).left) ∧
      (∀ {A B : smallEtaleSite (ofOver U)} (a : A ⟶ B),
        a.left.left ≫ (chartHom U B).left = (chartHom U A).left) := sorry

/-- The scheme étale chart recovered from a chart over the represented algebraic space. -/
def siteInverseObj (A : smallEtaleSite (ofOver U)) : U.left.Etale :=
  MorphismProperty.Over.mk ⊤ (chartHom U A).left ((siteInverse_laws U).1 A)

/-- The inverse site comparison retains the actual underlying scheme maps. -/
def siteInverse : smallEtaleSite (ofOver U) ⥤ U.left.Etale where
  obj := siteInverseObj U
  map a := MorphismProperty.Over.homMk a.left.left ((siteInverse_laws U).2 a)
  map_id _ := MorphismProperty.Over.Hom.ext rfl
  map_comp _ _ := MorphismProperty.Over.Hom.ext rfl

/-- The recovered chart and the original chart are isomorphic over the base
by the identity of their underlying scheme. -/
private def chartOverIso (A : smallEtaleSite (ofOver U)) :
    ((schemeEtaleToSmallEtale U).obj ((siteInverse U).obj A)).left ≅ A.left :=
  Over.isoMk (Iso.refl A.left.left)
    ((Category.id_comp A.left.hom).trans (chartHom U A).w.symm)

/-- The recovered chart maps give identity-on-scheme comparisons in both directions. -/
private theorem siteEquivalence_laws :
    (∀ W : U.left.Etale,
      𝟙 W.left ≫ ((siteInverse U).obj ((schemeEtaleToSmallEtale U).obj W)).hom = W.hom) ∧
      (∀ A : smallEtaleSite (ofOver U),
        (ofOverFunctor S).map (chartOverIso U A).hom ≫ A.hom =
          ((schemeEtaleToSmallEtale U).obj ((siteInverse U).obj A)).hom) := sorry

/-- The unit chart isomorphism is the identity on the underlying scheme. -/
private def siteUnit (W : U.left.Etale) :
    W ≅ (siteInverse U).obj ((schemeEtaleToSmallEtale U).obj W) :=
  MorphismProperty.Over.isoMk (Iso.refl _) ((siteEquivalence_laws U).1 W)

/-- The recovered chart isomorphism retains the identity on its underlying scheme. -/
private def siteCounit (A : smallEtaleSite (ofOver U)) :
    (schemeEtaleToSmallEtale U).obj ((siteInverse U).obj A) ≅ A :=
  MorphismProperty.CostructuredArrow.isoMk
    (chartOverIso U A) trivial trivial ((siteEquivalence_laws U).2 A)

/-- The small étale chart site of a represented scheme is equivalent to the
usual scheme small étale site, through recovery of the chart maps by Yoneda. -/
def siteEquivalence : U.left.Etale ≌ smallEtaleSite (ofOver U) where
  functor := schemeEtaleToSmallEtale U
  inverse := siteInverse U
  unitIso := NatIso.ofComponents (siteUnit U)
    (fun a ↦ MorphismProperty.Over.Hom.ext
      ((Category.comp_id a.left).trans (Category.id_comp a.left).symm))
  counitIso := NatIso.ofComponents (siteCounit U)
    (fun a ↦ MorphismProperty.CostructuredArrow.Hom.ext (Over.OverMorphism.ext
      ((Category.comp_id a.left.left).trans (Category.id_comp a.left.left).symm)))
  functor_unitIso_comp _ := MorphismProperty.CostructuredArrow.Hom.ext
    (Over.OverMorphism.ext (Category.id_comp _))

/-- Recovered charts preserve the small étale topologies. -/
private theorem fromScheme_laws :
    IsMorphismOfSites (smallEtaleTopology (ofOver U)) U.left.smallEtaleTopology
      (siteInverse U) := sorry

/-- The recovered-chart functor is the coherent inverse morphism of small étale sites. -/
instance siteInverse_isMorphismOfSites :
    IsMorphismOfSites (smallEtaleTopology (ofOver U)) U.left.smallEtaleTopology
      (siteInverse U) := fromScheme_laws U

/-- Recovery of a represented chart leaves its underlying scheme unchanged. -/
private def inverseProjection : siteInverse U ⋙ Scheme.smallEtaleToScheme U.left ⟶
    smallEtaleToScheme (ofOver U) where
  app _ := 𝟙 _
  naturality _ _ a := (Category.comp_id a.left.left).trans
    (Category.id_comp a.left.left).symm

/-- The reverse ringed-site comparison is induced by the actual recovered chart maps. -/
private def inverseRingedHom :
    RingedSite.Hom (Scheme.Etale.Small.ringedSite U.left) (ringedSite (ofOver U)) :=
  Scheme.Site.ringedHom (smallEtaleTopology (ofOver U)) U.left.smallEtaleTopology
    (smallEtaleToScheme (ofOver U)) (Scheme.smallEtaleToScheme U.left)
    (siteInverse U) (inverseProjection U)
    (structurePresheaf_isSheaf (ofOver U))
    (Scheme.Etale.Small.structurePresheaf_isSheaf U.left)

/-- Restriction to scheme charts, with its actual scalar comparison. -/
def toScheme : Modules (ofOver U) ⥤
    RingedSite.ModuleCat.{u} (Scheme.Etale.Small.ringedSite U.left) :=
  (schemeEtaleRingedHom U).modulePushforward

/-- Extension from the scheme small étale site evaluates on the recovered chart,
with scalars transported along the identity of its underlying scheme. -/
def fromScheme : RingedSite.ModuleCat.{u} (Scheme.Etale.Small.ringedSite U.left) ⥤
    Modules (ofOver U) :=
  (inverseRingedHom U).modulePushforward

/-- The structure-sheaf squares for the chart-recovery adjunction. -/
private def forwardCoefficients : Prop :=
  whiskerRight (NatTrans.op (siteEquivalence U).toAdjunction.counit)
      (structureSheaf (ofOver U)).obj =
    (inverseRingedHom U).structureSheafMap.hom ≫
      (siteInverse U).op.whiskerLeft (schemeEtaleRingedHom U).structureSheafMap.hom ∧
    (schemeEtaleRingedHom U).structureSheafMap.hom ≫
        (schemeEtaleToSmallEtale U).op.whiskerLeft
          (inverseRingedHom U).structureSheafMap.hom ≫
        whiskerRight (NatTrans.op (siteEquivalence U).toAdjunction.unit)
          (Scheme.Etale.Small.structureSheaf U.left).obj = 𝟙 _

/-- The structure-sheaf squares for the inverse chart-recovery adjunction. -/
private def reverseCoefficients : Prop :=
  whiskerRight (NatTrans.op (siteEquivalence U).symm.toAdjunction.counit)
      (Scheme.Etale.Small.structureSheaf U.left).obj =
    (schemeEtaleRingedHom U).structureSheafMap.hom ≫
      (schemeEtaleToSmallEtale U).op.whiskerLeft
        (inverseRingedHom U).structureSheafMap.hom ∧
    (inverseRingedHom U).structureSheafMap.hom ≫
        (siteInverse U).op.whiskerLeft (schemeEtaleRingedHom U).structureSheafMap.hom ≫
        whiskerRight (NatTrans.op (siteEquivalence U).symm.toAdjunction.unit)
          (structureSheaf (ofOver U)).obj = 𝟙 _

/-- Restriction and recovered-chart extension are adjoint through the actual
site unit, counit, and compatible scalar maps. -/
private def forwardAdjunction (h : forwardCoefficients U) : toScheme U ⊣ fromScheme U :=
  SheafOfModules.pushforwardPushforwardAdj
    (F := schemeEtaleToSmallEtale U) (G := siteInverse U) (siteEquivalence U).toAdjunction
    (schemeEtaleRingedHom U).structureSheafMap
    (inverseRingedHom U).structureSheafMap h.1 h.2

/-- Recovered-chart extension and restriction are adjoint in the reverse direction. -/
private def reverseAdjunction (h : reverseCoefficients U) : fromScheme U ⊣ toScheme U :=
  SheafOfModules.pushforwardPushforwardAdj
    (F := siteInverse U) (G := schemeEtaleToSmallEtale U) (siteEquivalence U).symm.toAdjunction
    (inverseRingedHom U).structureSheafMap
    (schemeEtaleRingedHom U).structureSheafMap h.1 h.2

/-- Chart recovery respects the structure sheaf, and the two induced
module adjunctions have mutually inverse units and counits. -/
private theorem equivalence_laws :
    (forwardCoefficients U ∧ reverseCoefficients U) ∧
      ∀ (hf : forwardCoefficients U) (hr : reverseCoefficients U),
        (forwardAdjunction U hf).unit ≫ (reverseAdjunction U hr).counit = 𝟙 _ ∧
        (reverseAdjunction U hr).counit ≫ (forwardAdjunction U hf).unit = 𝟙 _ ∧
        (forwardAdjunction U hf).counit ≫ (reverseAdjunction U hr).unit = 𝟙 _ ∧
        (reverseAdjunction U hr).unit ≫ (forwardAdjunction U hf).counit = 𝟙 _ := sorry

/-- Small étale modules on the represented algebraic space are equivalent to
scheme small étale modules, with explicit recovered-chart extension as inverse. -/
def equivalence : Modules (ofOver U) ≌
    RingedSite.ModuleCat.{u} (Scheme.Etale.Small.ringedSite U.left) :=
  let af := forwardAdjunction U (equivalence_laws U).1.1
  let ar := reverseAdjunction U (equivalence_laws U).1.2
  let h := (equivalence_laws U).2 (equivalence_laws U).1.1 (equivalence_laws U).1.2
  { functor := toScheme U
    inverse := fromScheme U
    unitIso := { hom := af.unit, inv := ar.counit, hom_inv_id := h.1, inv_hom_id := h.2.1 }
    counitIso :=
      { hom := af.counit, inv := ar.unit, hom_inv_id := h.2.2.1, inv_hom_id := h.2.2.2 }
    functor_unitIso_comp := af.left_triangle_components }

/-- The recovered-chart scalar map is the identity, and extension restrictions
are the original scheme-module restrictions on the recovered chart maps. -/
theorem evaluation_laws :
    (∀ A : smallEtaleSite (ofOver U),
      ((inverseRingedHom U).structureSheafMap.hom.app (op A)).hom = RingHom.id _) ∧
      (∀ (M : RingedSite.ModuleCat.{u} (Scheme.Etale.Small.ringedSite U.left))
        {A B : smallEtaleSite (ofOver U)} (a : A ⟶ B)
        (s : ((fromScheme U).obj M).val.obj (op B)),
        ((fromScheme U).obj M).val.map a.op s =
          M.val.map ((siteInverse U).map a).op s) := sorry

/-- Evaluation of represented-scheme extension is the original module on the
recovered chart, through the identity scalar comparison. -/
def evaluation (M : RingedSite.ModuleCat.{u} (Scheme.Etale.Small.ringedSite U.left))
    (A : smallEtaleSite (ofOver U)) :
    ((fromScheme U).obj M).val.obj (op A) ≅ M.val.obj (op ((siteInverse U).obj A)) :=
  (_root_.ModuleCat.restrictScalarsId'
    ((inverseRingedHom U).structureSheafMap.hom.app (op A)).hom
    ((evaluation_laws U).1 A)).app (M.val.obj (op ((siteInverse U).obj A)))

variable {U} {V : Over S}

open DerivedQCoh.SchemeRestriction CategoryTheory.Limits

/-- The chart-restriction composite following the explicit scheme pullback. -/
private def leftRinged (h : U ⟶ V) :=
  RingedSite.Hom.comp (ofOverRingedHom h) (schemeEtaleRingedHom V)

/-- The scheme pullback following restriction to scheme charts. -/
private def rightRinged (h : U ⟶ V) :=
  RingedSite.Hom.comp (schemeEtaleRingedHom U) (Scheme.Etale.Small.ringedHom h.left)

/-- The two scheme pullbacks in the comparison square are related by the
canonical symmetry and recovery of the original chart map. -/
private def pullbackChartIso (h : U ⟶ V) (W : V.left.Etale) :
    (((leftRinged h).base.obj W).left.left) ≅
      (((rightRinged h).base.obj W).left.left) :=
  pullback.congrHom rfl
      ((Category.id_comp _).symm.trans ((siteEquivalence_laws V).1 W)) ≪≫
    pullbackSymmetry h.left W.hom

/-- The canonical chart comparison commutes with the maps to the fixed base scheme. -/
private def pullbackOverConditions (h : U ⟶ V) : Prop :=
  ∀ W : V.left.Etale, (pullbackChartIso h W).hom ≫
    ((rightRinged h).base.obj W).left.hom = ((leftRinged h).base.obj W).left.hom

/-- The chart comparison over the fixed base, using the actual scheme pullback symmetry. -/
private def pullbackOverIso (h : U ⟶ V) (ho : pullbackOverConditions h)
    (W : V.left.Etale) :
    ((leftRinged h).base.obj W).left ≅ ((rightRinged h).base.obj W).left :=
  Over.isoMk (pullbackChartIso h W) (ho W)

/-- The chart comparison commutes with the structural map to the represented source. -/
private def pullbackChartConditions (h : U ⟶ V) (ho : pullbackOverConditions h) : Prop :=
  ∀ W : V.left.Etale, (ofOverFunctor S).map (pullbackOverIso h ho W).hom ≫
    ((rightRinged h).base.obj W).hom = ((leftRinged h).base.obj W).hom

/-- The fibre-product symmetry is an isomorphism of represented-source étale charts. -/
private def pullbackSiteIso (h : U ⟶ V) (ho : pullbackOverConditions h)
    (hc : pullbackChartConditions h ho) (W : V.left.Etale) :
    (leftRinged h).base.obj W ≅ (rightRinged h).base.obj W :=
  MorphismProperty.CostructuredArrow.isoMk (pullbackOverIso h ho W)
    trivial trivial (hc W)

/-- Naturality of the canonical fibre-product chart isomorphisms. -/
private def pullbackBaseNaturality (h : U ⟶ V) (ho : pullbackOverConditions h)
    (hc : pullbackChartConditions h ho) : Prop :=
  ∀ {W Z : V.left.Etale} (a : W ⟶ Z),
    (leftRinged h).base.map a ≫ (pullbackSiteIso h ho hc Z).hom =
      (pullbackSiteIso h ho hc W).hom ≫ (rightRinged h).base.map a

/-- The canonical comparison between the two base functors in the ringed-site square. -/
private def pullbackBaseIso (h : U ⟶ V) (ho : pullbackOverConditions h)
    (hc : pullbackChartConditions h ho) (hn : pullbackBaseNaturality h ho hc) :
    (leftRinged h).base ≅ (rightRinged h).base :=
  NatIso.ofComponents (pullbackSiteIso h ho hc) hn

/-- The explicit direct-image section comparisons are mutually inverse and natural. -/
private def comparisonLaws (h : U ⟶ V) : Prop :=
  (∀ M : Modules (ofOver U),
    ofOverPushforwardHom h M ≫ ofOverPushforwardInv h M = 𝟙 _ ∧
      ofOverPushforwardInv h M ≫ ofOverPushforwardHom h M = 𝟙 _) ∧
    (∀ {M N : Modules (ofOver U)} (a : M ⟶ N),
      (Modules.pushforward (ofOverMap h)).map a ≫ ofOverPushforwardHom h N =
        ofOverPushforwardHom h M ≫ (ofOverRingedHom h).modulePushforward.{u}.map a)

/-- Algebraic-space direct image agrees with the explicit represented scheme pullback
through evaluation and the right-Kan counit on the actual fibre product. -/
private def comparisonIso (h : U ⟶ V) (hl : comparisonLaws h) :
    Modules.pushforward (ofOverMap h) ≅ (ofOverRingedHom h).modulePushforward.{u} :=
  NatIso.ofComponents (fun M ↦
    { hom := ofOverPushforwardHom h M
      inv := ofOverPushforwardInv h M
      hom_inv_id := (hl.1 M).1
      inv_hom_id := (hl.1 M).2 }) hl.2

/-- The fibre-product chart comparisons are natural over the source, respect
regular-function restriction, and give inverse direct-image section maps. -/
private theorem pushforwardIso_laws (h : U ⟶ V) :
    pullbackOverConditions h ∧ ∀ ho : pullbackOverConditions h,
      pullbackChartConditions h ho ∧ ∀ hc : pullbackChartConditions h ho,
        pullbackBaseNaturality h ho hc ∧ ∀ hn : pullbackBaseNaturality h ho hc,
          (rightRinged h).structureSheafMap ≫
              (@Functor.sheafPushforwardContinuousNatTrans _ _ _ _
                (leftRinged h).base (rightRinged h).base
                (pullbackBaseIso h ho hc hn).hom RingCat.{u} inferInstance
                V.left.smallEtaleTopology (smallEtaleTopology (ofOver U))
                (RingedSite.Hom.base_isContinuous (leftRinged h))
                (RingedSite.Hom.base_isContinuous (rightRinged h))).app
                  (structureSheaf (ofOver U)) = (leftRinged h).structureSheafMap ∧
            comparisonLaws h := sorry

/-- Restriction to scheme charts commutes with module direct image, using the
actual fibre-product comparison and its coefficient compatibility. -/
def pushforwardIso (h : U ⟶ V) :
    Modules.pushforward (ofOverMap h) ⋙ toScheme V ≅
      toScheme U ⋙ (Scheme.Etale.Small.ringedHom h.left).modulePushforward.{u} :=
  let ho := (pushforwardIso_laws h).1
  let hc := ((pushforwardIso_laws h).2 ho).1
  let hn : pullbackBaseNaturality h ho hc := (((pushforwardIso_laws h).2 ho).2 hc).1
  let hs := (((pushforwardIso_laws h).2 ho).2 hc).2 hn
  isoWhiskerRight (comparisonIso h hs.2) (toScheme V) ≪≫
    RingedSite.Hom.modulePushforwardCompIso (ofOverRingedHom h) (schemeEtaleRingedHom V) ≪≫
    (@SheafOfModules.pushforwardCongr₂ _ _ _ _
      V.left.smallEtaleTopology (smallEtaleTopology (ofOver U))
      (leftRinged h).base (rightRinged h).base
      (Scheme.Etale.Small.structureSheaf V.left) (structureSheaf (ofOver U))
      (RingedSite.Hom.base_isContinuous (leftRinged h))
      (RingedSite.Hom.base_isContinuous (rightRinged h))
      (rightRinged h).structureSheafMap (leftRinged h).structureSheafMap
      (pullbackBaseIso h ho hc hn) hs.1).symm ≪≫
    (RingedSite.Hom.modulePushforwardCompIso (schemeEtaleRingedHom U)
      (Scheme.Etale.Small.ringedHom h.left)).symm

/-- The adjunction for extension to represented schemes followed by algebraic-space pullback. -/
private def spacePullbackAdjunction (h : U ⟶ V) :
    fromScheme V ⋙ Modules.pullback (ofOverMap h) ⊣
      Modules.pushforward (ofOverMap h) ⋙ toScheme V :=
  (equivalence V).symm.toAdjunction.comp (Modules.pullbackPushforwardAdjunction (ofOverMap h))

/-- The adjunction for scheme pullback followed by recovered-chart extension. -/
private def schemePullbackAdjunction (h : U ⟶ V) :
    (Scheme.Etale.Small.ringedHom h.left).modulePullback.{u} ⋙ fromScheme U ⊣
      toScheme U ⋙ (Scheme.Etale.Small.ringedHom h.left).modulePushforward.{u} :=
  (RingedSite.Hom.modulePullbackPushforwardAdjunction
    (Scheme.Etale.Small.ringedHom h.left)).comp (equivalence U).symm.toAdjunction

/-- Recovered-chart extension commutes with module pullback by the unique
left-adjoint comparison induced by the actual direct-image square. -/
def pullbackIso (h : U ⟶ V) :
    fromScheme V ⋙ Modules.pullback (ofOverMap h) ≅
      (Scheme.Etale.Small.ringedHom h.left).modulePullback.{u} ⋙ fromScheme U :=
  Adjunction.leftAdjointUniq
    ((spacePullbackAdjunction h).ofNatIsoRight (pushforwardIso h))
    (schemePullbackAdjunction h)

/-- The inverse-image comparison is the adjoint mate of the specified
direct-image comparison, on every module morphism. -/
theorem pullbackIso_laws (h : U ⟶ V)
    (M : RingedSite.ModuleCat.{u} (Scheme.Etale.Small.ringedSite V.left))
    (N : Modules (ofOver U))
    (a : ((Scheme.Etale.Small.ringedHom h.left).modulePullback.{u} ⋙
      fromScheme U).obj M ⟶ N) :
    (spacePullbackAdjunction h).homEquiv M N ((pullbackIso h).hom.app M ≫ a) =
      (schemePullbackAdjunction h).homEquiv M N a ≫ (pushforwardIso h).inv.app N := sorry

/-- Recovered-chart pullback comparisons preserve composition and identities,
with the canonical scheme and algebraic-space pullback isomorphisms. -/
theorem pullbackIso_coherence {W : Over S} (h : U ⟶ V) (k : V ⟶ W) :
    (isoWhiskerRight (pullbackIso k) (Modules.pullback (ofOverMap h)) ≪≫
      Functor.associator (Scheme.Etale.Small.ringedHom k.left).modulePullback.{u}
        (fromScheme V) (Modules.pullback (ofOverMap h)) ≪≫
      isoWhiskerLeft (Scheme.Etale.Small.ringedHom k.left).modulePullback.{u} (pullbackIso h) ≪≫
      (Functor.associator (Scheme.Etale.Small.ringedHom k.left).modulePullback.{u}
        (Scheme.Etale.Small.ringedHom h.left).modulePullback.{u} (fromScheme U)).symm ≪≫
      isoWhiskerRight (Scheme.Etale.Small.modulePullbackCompIso h.left k.left).symm
        (fromScheme U) =
    Functor.associator (fromScheme W) (Modules.pullback (ofOverMap k))
        (Modules.pullback (ofOverMap h)) ≪≫
      isoWhiskerLeft (fromScheme W)
        (Modules.pullbackCompIso (ofOverMap h) (ofOverMap k) ≪≫
          eqToIso (congrArg Modules.pullback ((ofOverFunctor S).map_comp h k).symm)) ≪≫
      pullbackIso (h ≫ k)) ∧
    (pullbackIso (𝟙 U) ≪≫
      isoWhiskerRight (Scheme.Etale.Small.modulePullbackIdIso U.left) (fromScheme U) ≪≫
      Functor.leftUnitor (fromScheme U) =
        isoWhiskerLeft (fromScheme U)
          (eqToIso (congrArg Modules.pullback ((ofOverFunctor S).map_id U)) ≪≫
            Modules.pullbackIdIso (ofOver U)) ≪≫ Functor.rightUnitor (fromScheme U)) := sorry

/-- Recovered-chart extension preserves and reflects quasi-coherence. -/
theorem isQuasicoherent_iff
    (M : RingedSite.ModuleCat.{u} (Scheme.Etale.Small.ringedSite U.left)) :
    ((fromScheme U).obj M).IsQuasicoherent ↔ M.IsQuasicoherent := sorry

end AlgebraicGeometry.AlgebraicSpace.SchemeEtaleModules
