/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.AtlasPoint
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.PointMap

/-!
# Reconstruct the local atlas lift of an original relative-spectrum point

Pull the supplied atlas back along the point's actual base map. On each affine
atlas open, evaluate the supplied descended algebra-map component on the real
pullback chart, then glue those ring maps into the point on the concrete atlas
spectrum. No inverse of the global restriction-bijectivity theorem is used.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite RingedSpace
open AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Over S}

/-- The actual base arrow of the original relative-spectrum point. -/
def relativeSpectrumPointBase (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T) : ofOver T ⟶ X :=
  yonedaEquiv.symm p.1

/-- Pull the stored atlas back along the point's base arrow using its supplied representability data. -/
def relativeSpectrumPointAtlasOver (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T) : Over S :=
  (atlasHom_presheaf_etale X).rep.pullback (relativeSpectrumPointBase A p)

/-- The actual projection of the point's atlas pullback to the stored atlas. -/
def relativeSpectrumPointAtlasToAtlas (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T) :
    relativeSpectrumPointAtlasOver A p ⟶ atlasScheme X :=
  (atlasHom_presheaf_etale X).rep.fst' (relativeSpectrumPointBase A p)

/-- The actual projection of the point's atlas pullback to its test scheme. -/
def relativeSpectrumPointAtlasToTest (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T) :
    relativeSpectrumPointAtlasOver A p ⟶ T :=
  (atlasHom_presheaf_etale X).rep.snd (relativeSpectrumPointBase A p)

/-- The inverse-image scheme of an atlas open, viewed over S. -/
def relativeSpectrumPointAtlasOpenOver (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T)
    (P : (atlasScheme X).left.Opens) : Over S :=
  Over.mk (((relativeSpectrumPointAtlasToAtlas A p).left ⁻¹ᵁ P).ι ≫
    (relativeSpectrumPointAtlasOver A p).hom)

/-- The pulled-back atlas open as an actual étale chart of the test scheme. -/
def relativeSpectrumPointAtlasOpenChart (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T)
    (P : (atlasScheme X).left.Opens) : smallEtaleSite (ofOver T) :=
  @smallEtaleSite.mk S (ofOver T) (relativeSpectrumPointAtlasOpenOver A p P)
    ((ofOverFunctor S).map (Over.homMk
      (((relativeSpectrumPointAtlasToAtlas A p).left ⁻¹ᵁ P).ι ≫
        (relativeSpectrumPointAtlasToTest A p).left) (by
          rw [Category.assoc, Over.w]
          rfl))) (by
      letI : (MorphismProperty.over (@AlgebraicGeometry.Etale) (X := S)).IsStableUnderComposition :=
        inferInstanceAs ((MorphismProperty.inverseImage (@AlgebraicGeometry.Etale)
          (Over.forget S)).IsStableUnderComposition)
      letI : (MorphismProperty.over (@AlgebraicGeometry.Etale) (X := S)).IsStableUnderBaseChange :=
        ⟨fun h hg ↦ MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Etale)
          (h.map (Over.forget S)) hg⟩
      haveI : AlgebraicGeometry.Etale (relativeSpectrumPointAtlasToTest A p).left :=
        (atlasHom_presheaf_etale X).property_snd (relativeSpectrumPointBase A p)
      exact ⟨fun _ hφ ↦ MorphismProperty.comp_mem _ _ _ hφ
        (MorphismProperty.relative_map (F := yoneda)
          (show AlgebraicGeometry.Etale
            (((relativeSpectrumPointAtlasToAtlas A p).left ⁻¹ᵁ P).ι ≫
              (relativeSpectrumPointAtlasToTest A p).left) from inferInstance))⟩)

/-- The pullback open's actual scheme map to the corresponding atlas open. -/
def relativeSpectrumPointAtlasOpenToAtlasOpen (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T)
    (P : (atlasScheme X).left.Opens) :
    relativeSpectrumPointAtlasOpenOver A p P ⟶ atlasOpenOver X P :=
  Over.homMk ((relativeSpectrumPointAtlasToAtlas A p).left ∣_ P) (by
    change (relativeSpectrumPointAtlasToAtlas A p).left ∣_ P ≫
      (P.ι ≫ (atlasScheme X).hom) =
        ((relativeSpectrumPointAtlasToAtlas A p).left ⁻¹ᵁ P).ι ≫
          (relativeSpectrumPointAtlasOver A p).hom
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w])

/-- The actual morphism from the pullback open into the space-étale base-change object. -/
def relativeSpectrumPointAtlasOpenEvaluationArrow (A : X.QcAlgebraUnder)
    (p : relativeSpectrumPair A T) (P : (atlasScheme X).left.Opens) :
    (smallEtaleToSpaces (ofOver T)).obj (relativeSpectrumPointAtlasOpenChart A p P) ⟶
      (etaleBaseChange (relativeSpectrumPointBase A p)).obj (atlasOpenToSmallEtaleObj X P) :=
  MorphismProperty.Over.homMk
    ((pullback.lift (relativeSpectrumPointAtlasOpenChart A p P).hom
      ((ofOverFunctor S).map (relativeSpectrumPointAtlasOpenToAtlasOpen A p P)) (by
        let j : relativeSpectrumPointAtlasOpenOver A p P ⟶ relativeSpectrumPointAtlasOver A p :=
          Over.homMk ((relativeSpectrumPointAtlasToAtlas A p).left ⁻¹ᵁ P).ι rfl
        have h : relativeSpectrumPointAtlasOpenToAtlasOpen A p P ≫ atlasOpenOverHom X P =
            j ≫ relativeSpectrumPointAtlasToAtlas A p := by
          apply Over.OverMorphism.ext
          exact morphismRestrict_ι _ _
        change yoneda.map (j ≫ relativeSpectrumPointAtlasToTest A p) ≫
            relativeSpectrumPointBase A p =
          yoneda.map (relativeSpectrumPointAtlasOpenToAtlasOpen A p P) ≫
            (yoneda.map (atlasOpenOverHom X P) ≫ atlasHom X)
        calc
          _ = yoneda.map j ≫ (yoneda.map (relativeSpectrumPointAtlasToTest A p) ≫
              relativeSpectrumPointBase A p) := by
            rw [Functor.map_comp, Category.assoc]
          _ = yoneda.map j ≫ (yoneda.map (relativeSpectrumPointAtlasToAtlas A p) ≫
              atlasHom X) :=
            congrArg (fun k ↦ yoneda.map j ≫ k)
              ((atlasHom_presheaf_etale X).rep.isPullback' (relativeSpectrumPointBase A p)).w.symm
          _ = _ := by
            rw [← Category.assoc, ← Functor.map_comp, ← h, Functor.map_comp, Category.assoc]) :
        yoneda.obj (relativeSpectrumPointAtlasOpenOver A p P) ⟶
          (etaleBaseChangeSpace (relativeSpectrumPointBase A p)
            (atlasOpenToSmallEtaleObj X P)).functorOfPoints)) (by
    exact pullback.lift_fst (f := homFunctor (relativeSpectrumPointBase A p))
      (g := homFunctor (atlasOpenToSmallEtaleObj X P).hom) _ _ _)

/-- The point's actual descended atlas component evaluated on its represented pullback open. -/
def relativeSpectrumPointAtlasSectionMap (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T)
    (P : (atlasScheme X).left.Opens) :
    sectionRing A (atlasOpenToSmallEtaleObj X P) ⟶
      Γ(((relativeSpectrumPointAtlasToAtlas A p).left ⁻¹ᵁ P).toScheme, ⊤) :=
  p.2.1.right.app (op P) ≫
    commRingPushforwardEvaluation (relativeSpectrumPointBase A p) (commStructureSheaf (ofOver T))
      (relativeSpectrumPointAtlasOpenEvaluationArrow A p P)

set_option backward.isDefEq.respectTransparency false in
private theorem relativeSpectrumPointEvaluation_naturality {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (R : Sheaf (smallEtaleTopology X) CommRingCat.{u})
    {U U' : smallEtaleSite X} {V V' : smallEtaleSite Y}
    (i : U' ⟶ U) (j : V' ⟶ V)
    (a : (smallEtaleToSpaces X).obj U ⟶ (etaleBaseChange f).obj V)
    (a' : (smallEtaleToSpaces X).obj U' ⟶ (etaleBaseChange f).obj V')
    (h : (smallEtaleToSpaces X).map i ≫ a = a' ≫ (etaleBaseChange f).map j) :
    ((commRingPushforward f).obj R).obj.map j.op ≫ commRingPushforwardEvaluation f R a' =
      commRingPushforwardEvaluation f R a ≫ R.obj.map i.op := by
  let Q := (commRingUnderlying X).obj R
  let E := (EtaleTopos.extension X).obj Q
  let η := ((commRingPushforwardUnderlyingIso f).hom.app R).hom
  let ε := ((EtaleTopos.extensionRestrictionIso X).hom.app Q).hom
  have hw : E.obj.map ((etaleBaseChange f).map j).op ≫ E.obj.map a'.op =
      E.obj.map a.op ≫ E.obj.map ((smallEtaleToSpaces X).map i).op := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, h]
  have H : ((commRingUnderlying Y).obj ((commRingPushforward f).obj R)).obj.map j.op ≫
        (η.app (op V') ≫ (E.obj.map a'.op ≫ ε.app (op U'))) =
      (η.app (op V) ≫ (E.obj.map a.op ≫ ε.app (op U))) ≫ Q.obj.map i.op := by
    calc
      _ = (((commRingUnderlying Y).obj ((commRingPushforward f).obj R)).obj.map j.op ≫
          η.app (op V')) ≫ E.obj.map a'.op ≫ ε.app (op U') := by
        simp only [Category.assoc]
      _ = (η.app (op V) ≫ E.obj.map ((etaleBaseChange f).map j).op) ≫
          E.obj.map a'.op ≫ ε.app (op U') := by
        exact congrArg (fun k ↦ k ≫ E.obj.map a'.op ≫ ε.app (op U')) (η.naturality j.op)
      _ = η.app (op V) ≫ (E.obj.map ((etaleBaseChange f).map j).op ≫
          E.obj.map a'.op) ≫ ε.app (op U') := by
        simp only [Category.assoc]
      _ = η.app (op V) ≫ (E.obj.map a.op ≫
          E.obj.map ((smallEtaleToSpaces X).map i).op) ≫ ε.app (op U') :=
        congrArg (fun k ↦ η.app (op V) ≫ k ≫ ε.app (op U')) hw
      _ = (η.app (op V) ≫ E.obj.map a.op) ≫
          (E.obj.map ((smallEtaleToSpaces X).map i).op ≫ ε.app (op U')) := by
        simp only [Category.assoc]
      _ = (η.app (op V) ≫ E.obj.map a.op) ≫ (ε.app (op U) ≫ Q.obj.map i.op) := by
        exact congrArg (fun k ↦ (η.app (op V) ≫ E.obj.map a.op) ≫ k) (ε.naturality i.op)
      _ = _ := by simp only [Category.assoc]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact congrArg (fun k ↦ k r) H

set_option backward.isDefEq.respectTransparency false in
private theorem relativeSpectrumPointAtlasSectionMap_naturality {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Over S}
    (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T)
    {P Q : (atlasScheme X).left.Opens} (i : P ⟶ Q) :
    (onChart A (relativeSpectrumAtlasChart X)).obj.right.obj.map i.op ≫
        relativeSpectrumPointAtlasSectionMap A p P ≫
          (Scheme.Opens.topIso ((relativeSpectrumPointAtlasToAtlas A p).left ⁻¹ᵁ P)).hom =
      (relativeSpectrumPointAtlasSectionMap A p Q ≫
          (Scheme.Opens.topIso ((relativeSpectrumPointAtlasToAtlas A p).left ⁻¹ᵁ Q)).hom) ≫
        (Under.mk (Hom.commRingSheafPushforwardMap
          (relativeSpectrumPointAtlasToAtlas A p).left.toShHom)).right.obj.map i.op := by
  let t := (relativeSpectrumPointAtlasToAtlas A p).left
  let hi := t.preimage_mono i.le
  let jOver : relativeSpectrumPointAtlasOpenOver A p P ⟶
      relativeSpectrumPointAtlasOpenOver A p Q :=
    Over.homMk ((relativeSpectrumPointAtlasOver A p).left.homOfLE hi) (by
      change (relativeSpectrumPointAtlasOver A p).left.homOfLE hi ≫
        ((t ⁻¹ᵁ Q).ι ≫ _) = (t ⁻¹ᵁ P).ι ≫ _
      rw [← Category.assoc, Scheme.homOfLE_ι])
  let j : relativeSpectrumPointAtlasOpenChart A p P ⟶
      relativeSpectrumPointAtlasOpenChart A p Q :=
    MorphismProperty.CostructuredArrow.homMk jOver trivial (by
      change yoneda.map jOver ≫ yoneda.map _ = yoneda.map _
      rw [← Functor.map_comp]
      congr 1
      apply Over.OverMorphism.ext
      change (relativeSpectrumPointAtlasOver A p).left.homOfLE hi ≫
        ((t ⁻¹ᵁ Q).ι ≫ _) = (t ⁻¹ᵁ P).ι ≫ _
      rw [← Category.assoc, Scheme.homOfLE_ι])
  let k := (atlasOpenToSmallEtale X).map i
  have hj : jOver ≫ relativeSpectrumPointAtlasOpenToAtlasOpen A p Q =
      relativeSpectrumPointAtlasOpenToAtlasOpen A p P ≫ k.left := by
    apply Over.OverMorphism.ext
    exact (morphismRestrict_homOfLE t P Q i.le).symm
  have hs : (smallEtaleToSpaces (ofOver T)).map j ≫
        relativeSpectrumPointAtlasOpenEvaluationArrow A p Q =
      relativeSpectrumPointAtlasOpenEvaluationArrow A p P ≫
        (etaleBaseChange (relativeSpectrumPointBase A p)).map k := by
    apply MorphismProperty.Over.Hom.ext
    change yoneda.map jOver ≫ (relativeSpectrumPointAtlasOpenEvaluationArrow A p Q).left =
      (relativeSpectrumPointAtlasOpenEvaluationArrow A p P).left ≫
        etaleBaseChangeMapNat (relativeSpectrumPointBase A p) k
    apply pullback.hom_ext (f := homFunctor (relativeSpectrumPointBase A p))
      (g := homFunctor (atlasOpenToSmallEtaleObj X Q).hom)
    · dsimp only [relativeSpectrumPointAtlasOpenEvaluationArrow, etaleBaseChangeMapNat,
        MorphismProperty.Over.homMk, CategoryTheory.Over.homMk]
      simp only [Category.assoc, pullback.map]
      erw [pullback.lift_fst, Category.assoc, pullback.lift_fst, Category.comp_id, pullback.lift_fst]
      exact smallEtaleSite.w j
    · dsimp only [relativeSpectrumPointAtlasOpenEvaluationArrow, etaleBaseChangeMapNat,
        MorphismProperty.Over.homMk, CategoryTheory.Over.homMk]
      simp only [Category.assoc, pullback.map]
      erw [pullback.lift_snd, Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd]
      change yoneda.map jOver ≫ yoneda.map (relativeSpectrumPointAtlasOpenToAtlasOpen A p Q) =
        yoneda.map (relativeSpectrumPointAtlasOpenToAtlasOpen A p P) ≫ yoneda.map k.left
      simpa only [Functor.map_comp] using congrArg yoneda.map hj
  have he := relativeSpectrumPointEvaluation_naturality (relativeSpectrumPointBase A p)
    (commStructureSheaf (ofOver T)) j k
    (relativeSpectrumPointAtlasOpenEvaluationArrow A p Q)
    (relativeSpectrumPointAtlasOpenEvaluationArrow A p P) hs
  have ht : (commStructureSheaf (ofOver T)).obj.map j.op ≫
        (Scheme.Opens.topIso (t ⁻¹ᵁ P)).hom =
      (Scheme.Opens.topIso (t ⁻¹ᵁ Q)).hom ≫
        (relativeSpectrumPointAtlasOver A p).left.presheaf.map (homOfLE hi).op := by
    exact (Scheme.restrictFunctorΓ (X := (relativeSpectrumPointAtlasOver A p).left)).hom.naturality
      (homOfLE hi).op
  have hm : (onChart A (relativeSpectrumAtlasChart X)).obj.right.obj.map i.op =
      (restrictUnder A.obj).right.map i.op := by
    change A.obj.right.obj.map ((chartOpens (relativeSpectrumAtlasChart X)).map i).op =
      A.obj.right.obj.map ((atlasOpenToSmallEtale X).map i).op
    congr 2
  have hp := p.2.1.right.naturality i.op
  change (restrictUnder A.obj).right.map i.op ≫ p.2.1.right.app (op P) =
    p.2.1.right.app (op Q) ≫ ((commRingPushforward (relativeSpectrumPointBase A p)).obj
      (commStructureSheaf (ofOver T))).obj.map k.op at hp
  dsimp only [relativeSpectrumPointAtlasSectionMap]
  calc
    _ = p.2.1.right.app (op Q) ≫
        (((commRingPushforward (relativeSpectrumPointBase A p)).obj
          (commStructureSheaf (ofOver T))).obj.map k.op ≫
          commRingPushforwardEvaluation (relativeSpectrumPointBase A p)
            (commStructureSheaf (ofOver T)) (relativeSpectrumPointAtlasOpenEvaluationArrow A p P)) ≫
        (Scheme.Opens.topIso (t ⁻¹ᵁ P)).hom := by
      simpa only [hm, t, Category.assoc] using congrArg
        (fun z ↦ z ≫ commRingPushforwardEvaluation (relativeSpectrumPointBase A p)
          (commStructureSheaf (ofOver T)) (relativeSpectrumPointAtlasOpenEvaluationArrow A p P) ≫
          (Scheme.Opens.topIso (t ⁻¹ᵁ P)).hom) hp
    _ = p.2.1.right.app (op Q) ≫
        (commRingPushforwardEvaluation (relativeSpectrumPointBase A p)
          (commStructureSheaf (ofOver T)) (relativeSpectrumPointAtlasOpenEvaluationArrow A p Q) ≫
          (commStructureSheaf (ofOver T)).obj.map j.op) ≫
        (Scheme.Opens.topIso (t ⁻¹ᵁ P)).hom := by rw [he]
    _ = _ := by
      simp only [Category.assoc]
      rw [ht]
      rfl

set_option backward.isDefEq.respectTransparency false in
private theorem relativeSpectrumPointStructureEvaluation {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {U : smallEtaleSite X} {V : smallEtaleSite Y}
    (a : (smallEtaleToSpaces X).obj U ⟶ (etaleBaseChange f).obj V) :
    (commStructureSheafMap f).hom.app (op V) ≫
        commRingPushforwardEvaluation f (commStructureSheaf X) a =
      commStructureFMap_app (etaleSquareOfArrow f V (StructuredArrow.mk a.op)) := by
  let Q := EtaleRingedTopos.structureTypes X
  let e := (ringPushforwardForgetIso f).app (structureSheaf X)
  have hfac : (EtaleRingedTopos.structureUnderlying f).hom.app (op V) ≫
        EtaleTopos.extensionEvaluation X Q a =
      TypeCat.ofHom
        (commStructureFMap_app (etaleSquareOfArrow f V (StructuredArrow.mk a.op))).hom := by
    exact (EtaleTopos.allChartIsLimit X Q ((etaleBaseChange f).obj V)).fac
      ((forget RingCat.{u}).mapCone (structureSheafMapCone f V)) (StructuredArrow.mk a.op)
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  change EtaleTopos.extensionEvaluation X Q a
      (e.hom.hom.app (op V) (e.inv.hom.app (op V)
        ((EtaleRingedTopos.structureUnderlying f).hom.app (op V) r))) = _
  rw [show e.hom.hom.app (op V) (e.inv.hom.app (op V)
      ((EtaleRingedTopos.structureUnderlying f).hom.app (op V) r)) =
        (EtaleRingedTopos.structureUnderlying f).hom.app (op V) r from
    congrArg (fun k ↦ k.hom.app (op V)
      ((EtaleRingedTopos.structureUnderlying f).hom.app (op V) r)) e.inv_hom_id]
  exact congrArg (fun k ↦ k r) hfac

set_option backward.isDefEq.respectTransparency false in
private theorem relativeSpectrumPointAtlasSectionMap_structure {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Over S}
    (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T) (P : (atlasScheme X).left.Opens) :
    (onChart A (relativeSpectrumAtlasChart X)).obj.hom.hom.app (op P) ≫
        (relativeSpectrumPointAtlasSectionMap A p P ≫
          (Scheme.Opens.topIso ((relativeSpectrumPointAtlasToAtlas A p).left ⁻¹ᵁ P)).hom) =
      (Hom.commRingSheafPushforwardMap (relativeSpectrumPointAtlasToAtlas A p).left.toShHom).hom.app
        (op P) := by
  let t := (relativeSpectrumPointAtlasToAtlas A p).left
  let a := relativeSpectrumPointAtlasOpenEvaluationArrow A p P
  let W := atlasOpenToSmallEtaleObj X P
  have ha : (etaleSquareOfArrow (relativeSpectrumPointBase A p) W
      (StructuredArrow.mk a.op)).map = relativeSpectrumPointAtlasOpenToAtlasOpen A p P := by
    change yonedaEquiv (a.left ≫ etaleBaseChangeSnd (relativeSpectrumPointBase A p) W) = _
    have hs : a.left ≫ etaleBaseChangeSnd (relativeSpectrumPointBase A p) W =
        yoneda.map (relativeSpectrumPointAtlasOpenToAtlasOpen A p P) := by
      exact pullback.lift_snd (f := homFunctor (relativeSpectrumPointBase A p))
        (g := homFunctor W.hom) _ _ _
    exact (congrArg yonedaEquiv hs).trans (yonedaEquiv_yoneda_map _)
  have he : structureMap A W ≫ p.2.1.right.app (op P) =
      (commStructureSheafMap (relativeSpectrumPointBase A p)).hom.app (op W) := by
    exact congrArg (fun z ↦ z.app (op P)) (Under.w p.2.1)
  have hs : (commStructureSheafMap (relativeSpectrumPointBase A p)).hom.app (op W) ≫
      commRingPushforwardEvaluation (relativeSpectrumPointBase A p)
        (commStructureSheaf (ofOver T)) a =
      (relativeSpectrumPointAtlasOpenToAtlasOpen A p P).left.appTop :=
    (relativeSpectrumPointStructureEvaluation (relativeSpectrumPointBase A p) a).trans
      (congrArg (fun z ↦ z.left.appTop) ha)
  have ht := (arrowResLEAppIso t P (t ⁻¹ᵁ P) le_rfl).hom.w.symm
  change (t.resLE P (t ⁻¹ᵁ P) le_rfl).appTop ≫ (Scheme.Opens.topIso (t ⁻¹ᵁ P)).hom =
    (Scheme.Opens.topIso P).hom ≫ t.appLE P (t ⁻¹ᵁ P) le_rfl at ht
  rw [Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appLE_eq_app] at ht
  change ((Scheme.Opens.topIso P).inv ≫ structureMap A W) ≫
    ((p.2.1.right.app (op P) ≫ commRingPushforwardEvaluation (relativeSpectrumPointBase A p)
      (commStructureSheaf (ofOver T)) a) ≫ (Scheme.Opens.topIso (t ⁻¹ᵁ P)).hom) = t.app P
  calc
    _ = (Scheme.Opens.topIso P).inv ≫
        ((commStructureSheafMap (relativeSpectrumPointBase A p)).hom.app (op W) ≫
          commRingPushforwardEvaluation (relativeSpectrumPointBase A p)
            (commStructureSheaf (ofOver T)) a) ≫ (Scheme.Opens.topIso (t ⁻¹ᵁ P)).hom := by
      simpa only [Category.assoc] using congrArg
        (fun z ↦ (Scheme.Opens.topIso P).inv ≫ z ≫
          commRingPushforwardEvaluation (relativeSpectrumPointBase A p)
            (commStructureSheaf (ofOver T)) a ≫ (Scheme.Opens.topIso (t ⁻¹ᵁ P)).hom) he
    _ = (Scheme.Opens.topIso P).inv ≫ (t ∣_ P).appTop ≫
        (Scheme.Opens.topIso (t ⁻¹ᵁ P)).hom := by rw [hs]; rfl
    _ = _ := by rw [ht, Iso.inv_hom_id_assoc]

/-- The actual algebra map on the atlas pullback, glued from the supplied point's original components. -/
def relativeSpectrumPointAtlasAlgebraMap (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T) :
    (onChart A (relativeSpectrumAtlasChart X)).obj ⟶ Under.mk
      (Hom.commRingSheafPushforwardMap (relativeSpectrumPointAtlasToAtlas A p).left.toShHom) :=
  Under.homMk
    ⟨{ app := fun P ↦ relativeSpectrumPointAtlasSectionMap A p P.unop ≫
        (Scheme.Opens.topIso ((relativeSpectrumPointAtlasToAtlas A p).left ⁻¹ᵁ P.unop)).hom
       naturality := by
         intro P Q i
         exact relativeSpectrumPointAtlasSectionMap_naturality A p i.unop }⟩ (by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext P
    exact relativeSpectrumPointAtlasSectionMap_structure A p P.unop)

/-- The actual lift of the original point to the concrete affine spectrum atlas. -/
def relativeSpectrumPointAtlasLift (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T) :
    relativeSpectrumPointAtlasOver A p ⟶ relativeSpectrumDescentAtlas A :=
  Over.homMk
    (Scheme.relativeSpectrumPointMap (onChart A (relativeSpectrumAtlasChart X))
      ⟨(relativeSpectrumPointAtlasToAtlas A p).left, relativeSpectrumPointAtlasAlgebraMap A p⟩) (by
    change Scheme.relativeSpectrumPointMap _ _ ≫
      ((Scheme.relativeSpectrumOver (onChart A (relativeSpectrumAtlasChart X))).π ≫
        (atlasScheme X).hom) = (relativeSpectrumPointAtlasOver A p).hom
    rw [← Category.assoc, Scheme.relativeSpectrumPointMap_toBase]
    exact Over.w (relativeSpectrumPointAtlasToAtlas A p))

/-- The local atlas lift is over the original test point's base morphism. -/
theorem relativeSpectrumPointAtlasLift_toX (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T) :
    (ofOverFunctor S).map (relativeSpectrumPointAtlasLift A p) ≫ relativeSpectrumDescentAtlasHomToX A =
      (ofOverFunctor S).map (relativeSpectrumPointAtlasToTest A p) ≫ relativeSpectrumPointBase A p := by
  have h : relativeSpectrumPointAtlasLift A p ≫
      Over.homMk (Scheme.relativeSpectrumOver (onChart A (relativeSpectrumAtlasChart X))).π rfl =
        relativeSpectrumPointAtlasToAtlas A p := by
    apply Over.OverMorphism.ext
    exact Scheme.relativeSpectrumPointMap_toBase _ _
  change yoneda.map (relativeSpectrumPointAtlasLift A p) ≫
      (yoneda.map (Over.homMk
        (Scheme.relativeSpectrumOver (onChart A (relativeSpectrumAtlasChart X))).π rfl) ≫
          atlasHom X) = _
  rw [← Category.assoc, ← Functor.map_comp, h]
  exact ((atlasHom_presheaf_etale X).rep.isPullback' (relativeSpectrumPointBase A p)).w

end AlgebraicGeometry.AlgebraicSpace
