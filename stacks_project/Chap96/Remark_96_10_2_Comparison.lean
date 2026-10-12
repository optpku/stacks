/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap66.Lemma_66_18_12_Restriction
public import stacks_project.Chap96.Lemma_96_10_3_Comparison

/-!
# Étale-localization square of ringed topoi

If `f : X ⟶ Y` is a 1-morphism of categories fibred in groupoids over
`(Sch/S)_fppf`, with `X` and `Y` represented by algebraic spaces `F` and `G`,
and the induced morphism `F ⟶ G` is étale, then the square of ringed topoi
with edges `f_small`, `i_F`, `i_G`, and `f` commutes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open Opposite FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}
variable {X Y : GroupoidsOver S} {F G : AlgebraicSpace S}
variable (eX : F.toGroupoids ≌ X) (eY : G.toGroupoids ≌ Y) (f : X ⟶ Y)
variable (α : (f ≫ eY.symm.hom) ≅
    (eX.symm.hom ≫ AlgebraicSpace.toGroupoids.map (inducedHom eX eY f)))
variable [AlgebraicSpace.Etale (inducedHom eX eY f)]
variable [HasSheafify (AlgebraicSpace.smallEtaleTopology F) (Type u)]
variable [HasSheafify (AlgebraicSpace.smallEtaleTopology G) (Type u)]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor F X eX).op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite G)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor G Y eY).op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ RingCat.{u},
    (smallEtaleFunctor F X eX).op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite G)ᵒᵖ ⥤ RingCat.{u},
    (smallEtaleFunctor G Y eY).op.HasPointwiseRightKanExtension P]
variable [(forget RingCat.{u}).PreservesRightKanExtensions (smallEtaleFunctor F X eX).op]
variable [(forget RingCat.{u}).PreservesRightKanExtensions (smallEtaleFunctor G Y eY).op]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor F X eX).op.HasLeftKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite G)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor G Y eY).op.HasLeftKanExtension P]
variable [∀ P : X.totalᵒᵖ ⥤ Type u,
    (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : F.toGroupoids.totalᵒᵖ ⥤ Type u,
    (toCartesianBasedFunctor
        (AlgebraicSpace.toGroupoids.map (inducedHom eX eY f))).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ Type u,
    (AlgebraicSpace.smallEtaleInclusion F).op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ Type u,
    (AlgebraicSpace.etaleRestriction (inducedHom eX eY f)).op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor F X eX ⋙ (toCartesianBasedFunctor f).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ Type u,
    (AlgebraicSpace.etaleRestriction (inducedHom eX eY f) ⋙
        smallEtaleFunctor G Y eY).op.HasPointwiseRightKanExtension P]

/-- The composite `u_F ⋙ f` is cocontinuous for the small étale topology of `F` and the
associated étale topology of `Y`. -/
instance smallEtaleFunctor_comp_toFunctor_isCocontinuous :
    (smallEtaleFunctor F X eX ⋙ (toCartesianBasedFunctor f).toFunctor).IsCocontinuous
      (AlgebraicSpace.smallEtaleTopology F) Y.etaleTopology :=
  isCocontinuous_comp (smallEtaleFunctor F X eX)
    (toCartesianBasedFunctor f).toFunctor
    (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology

/-- The composite `etaleRestriction ⋙ u_G` is cocontinuous for the small étale topology of `F`
and the associated étale topology of `Y`. -/
instance etaleRestriction_comp_smallEtaleFunctor_isCocontinuous :
    (AlgebraicSpace.etaleRestriction (inducedHom eX eY f) ⋙
        smallEtaleFunctor G Y eY).IsCocontinuous
      (AlgebraicSpace.smallEtaleTopology F) Y.etaleTopology :=
  isCocontinuous_comp
    (AlgebraicSpace.etaleRestriction (inducedHom eX eY f))
    (smallEtaleFunctor G Y eY)
    (AlgebraicSpace.smallEtaleTopology F) (AlgebraicSpace.smallEtaleTopology G)

/-- The object of `S_G` classified by `U ⟶ F ⟶ G` is the image of the object classified by
`U ⟶ F` under `toGroupoids.map`. -/
def smallEtaleToGroupoids_mapIso_app (U : AlgebraicSpace.smallEtaleSite F) :
    (toFunctor (AlgebraicSpace.toGroupoids.map (inducedHom eX eY f))).obj (toGroupoidsObj U) ≅
      toGroupoidsObj ((AlgebraicSpace.etaleRestriction (inducedHom eX eY f)).obj U) where
  hom :=
    Quiver.Hom.op
      (CategoryTheory.CategoryOfElements.homMk
        (unop (toGroupoidsObj ((AlgebraicSpace.etaleRestriction (inducedHom eX eY f)).obj U)))
        (unop ((toFunctor (AlgebraicSpace.toGroupoids.map (inducedHom eX eY f))).obj
            (toGroupoidsObj U)))
        (𝟙 _) sorry)
  inv :=
    Quiver.Hom.op
      (CategoryTheory.CategoryOfElements.homMk
        (unop ((toFunctor (AlgebraicSpace.toGroupoids.map (inducedHom eX eY f))).obj
            (toGroupoidsObj U)))
        (unop (toGroupoidsObj ((AlgebraicSpace.etaleRestriction (inducedHom eX eY f)).obj U)))
        (𝟙 _) sorry)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Postcomposition on `F_étale` with `toGroupoids.map (inducedHom eX eY f)` agrees with
`etaleRestriction` into `S_G`. -/
def smallEtaleToGroupoids_mapIso :
    smallEtaleToGroupoids F ⋙
        toFunctor (AlgebraicSpace.toGroupoids.map (inducedHom eX eY f)) ≅
      AlgebraicSpace.etaleRestriction (inducedHom eX eY f) ⋙ smallEtaleToGroupoids G :=
  NatIso.ofComponents (fun U => smallEtaleToGroupoids_mapIso_app eX eY f U) sorry

/-- Site-level identification `u_F ⋙ f ≅ etaleRestriction ⋙ u_G` induced by the presentation
`2`-iso `α`. -/
def compareInclusionFunctorIso :
    smallEtaleFunctor F X eX ⋙ (toCartesianBasedFunctor f).toFunctor ≅
      AlgebraicSpace.etaleRestriction (inducedHom eX eY f) ⋙ smallEtaleFunctor G Y eY :=
  isoWhiskerLeft (smallEtaleFunctor F X eX) (cartesianToFunctorIso f) ≪≫
    (Functor.associator (smallEtaleToGroupoids F) (toFunctor eX.hom) (toFunctor f)) ≪≫
      isoWhiskerLeft (smallEtaleToGroupoids F)
        (ObjectProperty.FullSubbicategory.toFunctor.compIso eX.hom f) ≪≫
        isoWhiskerLeft (smallEtaleToGroupoids F) (toFunctorIso (presentedTwoCell eX eY f α)) ≪≫
          isoWhiskerLeft (smallEtaleToGroupoids F)
            (ObjectProperty.FullSubbicategory.toFunctor.compIso
              (AlgebraicSpace.toGroupoids.map (inducedHom eX eY f)) eY.hom).symm ≪≫
            (Functor.associator (smallEtaleToGroupoids F)
                (toFunctor (AlgebraicSpace.toGroupoids.map (inducedHom eX eY f)))
                (toFunctor eY.hom)).symm ≪≫
              isoWhiskerRight (smallEtaleToGroupoids_mapIso eX eY f) (toFunctor eY.hom) ≪≫
                Functor.associator (AlgebraicSpace.etaleRestriction (inducedHom eX eY f))
                  (smallEtaleToGroupoids G) (toFunctor eY.hom)

/-- The comma category computing `etaleRestriction_* 𝒢` at `V`. -/
abbrev etaleRestrictionIndex (V : AlgebraicSpace.smallEtaleSite G) :=
  StructuredArrow (op V) (AlgebraicSpace.etaleRestriction (inducedHom eX eY f)).op

/-- The Kan diagram of a small étale sheaf along étale restriction at `V`. -/
abbrev etaleRestrictionDiag (𝒢 : Sheaf (AlgebraicSpace.smallEtaleTopology F) (Type u))
    (V : AlgebraicSpace.smallEtaleSite G) :
    etaleRestrictionIndex eX eY f V ⥤ Type u :=
  StructuredArrow.proj (op V) (AlgebraicSpace.etaleRestriction (inducedHom eX eY f)).op ⋙
    𝒢.obj

/-- The Kan diagram of a small étale sheaf along the spaces inclusion at `F ×_G V`. -/
abbrev etaleBaseChangeDiag (𝒢 : Sheaf (AlgebraicSpace.smallEtaleTopology F) (Type u))
    (V : AlgebraicSpace.smallEtaleSite G) :
    AlgebraicSpace.compareSmallIndex (inducedHom eX eY f) V ⥤ Type u :=
  StructuredArrow.proj (op ((AlgebraicSpace.etaleBaseChange (inducedHom eX eY f)).obj V))
      (AlgebraicSpace.smallEtaleInclusion F).op ⋙
    𝒢.obj

/-- The morphism `etaleRestriction(U) ⟶ V` associated to a small-étale comma object over
`F ×_G V`. -/
def etaleDirectImageIndexHom (V : AlgebraicSpace.smallEtaleSite G)
    (k : AlgebraicSpace.compareSmallIndex (inducedHom eX eY f) V) :
    (AlgebraicSpace.etaleRestriction (inducedHom eX eY f)).obj k.right.unop ⟶ V :=
  MorphismProperty.CostructuredArrow.homMk
    (AlgebraicSpace.compareOverHom (inducedHom eX eY f) k) trivial sorry

/-- The functor from the base-change Kan comma category to the étale-restriction Kan comma
category. -/
def etaleDirectImageIndexMap (V : AlgebraicSpace.smallEtaleSite G) :
    AlgebraicSpace.compareSmallIndex (inducedHom eX eY f) V ⥤
      etaleRestrictionIndex eX eY f V where
  obj k := StructuredArrow.mk (op (etaleDirectImageIndexHom eX eY f V k))
  map {k k'} τ := StructuredArrow.homMk τ.right sorry
  map_id := sorry
  map_comp := sorry

/-- The functor-of-points lift of an étale-restriction comma object into `F ×_G V`. -/
def etaleDirectImageLift (V : AlgebraicSpace.smallEtaleSite G)
    (k : etaleRestrictionIndex eX eY f V) :
    (AlgebraicSpace.ofOver k.right.unop.left).functorOfPoints ⟶
      AlgebraicSpace.etaleBaseChangeFunctorOfPoints (inducedHom eX eY f) V :=
  pullback.lift (AlgebraicSpace.homFunctor k.right.unop.hom)
    (AlgebraicSpace.homFunctor (AlgebraicSpace.ofOverMap k.hom.unop.left)) sorry

/-- The morphism `U ⟶ F ×_G V` of étale algebraic spaces associated to an étale-restriction
comma object. -/
def etaleDirectImageToBaseChange (V : AlgebraicSpace.smallEtaleSite G)
    (k : etaleRestrictionIndex eX eY f V) :
    (AlgebraicSpace.smallEtaleInclusion F).obj k.right.unop ⟶
      (AlgebraicSpace.etaleBaseChange (inducedHom eX eY f)).obj V :=
  MorphismProperty.Over.homMk (etaleDirectImageLift eX eY f V k) sorry

/-- The reverse functor from the étale-restriction Kan comma category to the base-change Kan
comma category. -/
def etaleDirectImageIndexInvMap (V : AlgebraicSpace.smallEtaleSite G) :
    etaleRestrictionIndex eX eY f V ⥤
      AlgebraicSpace.compareSmallIndex (inducedHom eX eY f) V where
  obj k := StructuredArrow.mk (op (etaleDirectImageToBaseChange eX eY f V k))
  map {k k'} τ := StructuredArrow.homMk τ.right sorry
  map_id := sorry
  map_comp := sorry

/-- After applying `etaleDirectImageIndexMap`, the étale-restriction diagram recovers the
base-change diagram. -/
def etaleDirectImageDiagIso (𝒢 : Sheaf (AlgebraicSpace.smallEtaleTopology F) (Type u))
    (V : AlgebraicSpace.smallEtaleSite G) :
    etaleDirectImageIndexMap eX eY f V ⋙ etaleRestrictionDiag eX eY f 𝒢 V ≅
      etaleBaseChangeDiag eX eY f 𝒢 V :=
  NatIso.ofComponents (fun _ => Iso.refl _) sorry

/-- After applying `etaleDirectImageIndexInvMap`, the base-change diagram recovers the
étale-restriction diagram. -/
def etaleDirectImageDiagInvIso (𝒢 : Sheaf (AlgebraicSpace.smallEtaleTopology F) (Type u))
    (V : AlgebraicSpace.smallEtaleSite G) :
    etaleDirectImageIndexInvMap eX eY f V ⋙ etaleBaseChangeDiag eX eY f 𝒢 V ≅
      etaleRestrictionDiag eX eY f 𝒢 V :=
  NatIso.ofComponents (fun _ => Iso.refl _) sorry

/-- Restriction of compatible families from the étale-restriction Kan comma category to the
base-change Kan comma category. -/
def etaleDirectImageLimitInv (𝒢 : Sheaf (AlgebraicSpace.smallEtaleTopology F) (Type u))
    (V : AlgebraicSpace.smallEtaleSite G) :
    limit (etaleRestrictionDiag eX eY f 𝒢 V) ⟶ limit (etaleBaseChangeDiag eX eY f 𝒢 V) :=
  limit.lift (etaleBaseChangeDiag eX eY f 𝒢 V)
    { pt := limit (etaleRestrictionDiag eX eY f 𝒢 V)
      π :=
        { app := fun k ↦
            limit.π (etaleRestrictionDiag eX eY f 𝒢 V)
                ((etaleDirectImageIndexMap eX eY f V).obj k) ≫
              (etaleDirectImageDiagIso eX eY f 𝒢 V).hom.app k
          naturality := sorry } }

/-- Extension of base-change compatible families to étale-restriction compatible families. -/
def etaleDirectImageLimitHom (𝒢 : Sheaf (AlgebraicSpace.smallEtaleTopology F) (Type u))
    (V : AlgebraicSpace.smallEtaleSite G) :
    limit (etaleBaseChangeDiag eX eY f 𝒢 V) ⟶ limit (etaleRestrictionDiag eX eY f 𝒢 V) :=
  limit.lift (etaleRestrictionDiag eX eY f 𝒢 V)
    { pt := limit (etaleBaseChangeDiag eX eY f 𝒢 V)
      π :=
        { app := fun k ↦
            limit.π (etaleBaseChangeDiag eX eY f 𝒢 V)
                ((etaleDirectImageIndexInvMap eX eY f V).obj k) ≫
              (etaleDirectImageDiagInvIso eX eY f 𝒢 V).hom.app k
          naturality := sorry } }

/-- Canonical identification of the two Type-`u` Kan-extension limits at `V`. -/
def etaleDirectImageLimitIso (𝒢 : Sheaf (AlgebraicSpace.smallEtaleTopology F) (Type u))
    (V : AlgebraicSpace.smallEtaleSite G) :
    limit (etaleBaseChangeDiag eX eY f 𝒢 V) ≅ limit (etaleRestrictionDiag eX eY f 𝒢 V) where
  hom := etaleDirectImageLimitHom eX eY f 𝒢 V
  inv := etaleDirectImageLimitInv eX eY f 𝒢 V
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Evaluation of `f_small,* 𝒢` at `V` recovers the base-change Kan limit. -/
def etaleDirectImageIso_leftEval (𝒢 : Sheaf (AlgebraicSpace.smallEtaleTopology F) (Type u))
    (V : AlgebraicSpace.smallEtaleSite G) :
    ((AlgebraicSpace.typePushforward (inducedHom eX eY f)).obj 𝒢).obj.obj (op V) ≅
      limit (etaleBaseChangeDiag eX eY f 𝒢 V) :=
  (AlgebraicSpace.EtaleTopos.allChartIsLimit F 𝒢
      ((AlgebraicSpace.etaleBaseChange (inducedHom eX eY f)).obj V)).conePointUniqueUpToIso
    (limit.isLimit (etaleBaseChangeDiag eX eY f 𝒢 V))

/-- Evaluation of `etaleRestriction_* 𝒢` at `V` recovers the étale-restriction Kan limit. -/
def etaleDirectImageIso_rightEval (𝒢 : Sheaf (AlgebraicSpace.smallEtaleTopology F) (Type u))
    (V : AlgebraicSpace.smallEtaleSite G) :
    (((AlgebraicSpace.etaleRestriction (inducedHom eX eY f)).sheafPushforwardCocontinuous
          (Type u) (AlgebraicSpace.smallEtaleTopology F)
          (AlgebraicSpace.smallEtaleTopology G)).obj 𝒢).obj.obj (op V) ≅
      limit (etaleRestrictionDiag eX eY f 𝒢 V) :=
  (((AlgebraicSpace.etaleRestriction (inducedHom eX eY f)).sheafPushforwardCocontinuousCompSheafToPresheafIso
        (Type u) (AlgebraicSpace.smallEtaleTopology F)
        (AlgebraicSpace.smallEtaleTopology G)).app 𝒢).app (op V) ≪≫
    (AlgebraicSpace.etaleRestriction (inducedHom eX eY f)).op.ranObjObjIsoLimit 𝒢.obj (op V)

/-- Sectionwise identification of `f_small,* 𝒢` with `etaleRestriction_* 𝒢`. -/
def etaleDirectImageIso_app (𝒢 : Sheaf (AlgebraicSpace.smallEtaleTopology F) (Type u))
    (V : AlgebraicSpace.smallEtaleSite G) :
    ((AlgebraicSpace.typePushforward (inducedHom eX eY f)).obj 𝒢).obj.obj (op V) ≅
      (((AlgebraicSpace.etaleRestriction (inducedHom eX eY f)).sheafPushforwardCocontinuous
          (Type u) (AlgebraicSpace.smallEtaleTopology F)
          (AlgebraicSpace.smallEtaleTopology G)).obj 𝒢).obj.obj (op V) :=
  etaleDirectImageIso_leftEval eX eY f 𝒢 V ≪≫
    etaleDirectImageLimitIso eX eY f 𝒢 V ≪≫
      (etaleDirectImageIso_rightEval eX eY f 𝒢 V).symm

/-- Underlying presheaf identification of `f_small,*` with cocontinuous pushforward along
étale restriction. -/
def etaleDirectImageIsoPresheaf (𝒢 : Sheaf (AlgebraicSpace.smallEtaleTopology F) (Type u)) :
    ((AlgebraicSpace.typePushforward (inducedHom eX eY f)).obj 𝒢).obj ≅
      (((AlgebraicSpace.etaleRestriction (inducedHom eX eY f)).sheafPushforwardCocontinuous
          (Type u) (AlgebraicSpace.smallEtaleTopology F)
          (AlgebraicSpace.smallEtaleTopology G)).obj 𝒢).obj :=
  NatIso.ofComponents (fun V => etaleDirectImageIso_app eX eY f 𝒢 V.unop) sorry

/-- The sheaf identification `f_small,* 𝒢 ≅ etaleRestriction_* 𝒢`. -/
def etaleDirectImageIso_obj (𝒢 : Sheaf (AlgebraicSpace.smallEtaleTopology F) (Type u)) :
    (AlgebraicSpace.typePushforward (inducedHom eX eY f)).obj 𝒢 ≅
      ((AlgebraicSpace.etaleRestriction (inducedHom eX eY f)).sheafPushforwardCocontinuous
          (Type u) (AlgebraicSpace.smallEtaleTopology F)
          (AlgebraicSpace.smallEtaleTopology G)).obj 𝒢 where
  hom := CategoryTheory.ObjectProperty.homMk (etaleDirectImageIsoPresheaf eX eY f 𝒢).hom
  inv := CategoryTheory.ObjectProperty.homMk (etaleDirectImageIsoPresheaf eX eY f 𝒢).inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- When `F ⟶ G` is étale, small étale direct image agrees with cocontinuous pushforward along
`etaleRestriction`. -/
def etaleDirectImageIso :
    AlgebraicSpace.typePushforward (inducedHom eX eY f) ≅
      (AlgebraicSpace.etaleRestriction (inducedHom eX eY f)).sheafPushforwardCocontinuous
        (Type u) (AlgebraicSpace.smallEtaleTopology F)
        (AlgebraicSpace.smallEtaleTopology G) :=
  NatIso.ofComponents (fun 𝒢 => etaleDirectImageIso_obj eX eY f 𝒢) sorry

/-- The canonical Type-`u` identification `i_{G,*} f_small,* ≅ f_* i_{F,*}` of direct images of
ringed topoi. -/
def compareInclusionIso :
    (RingedSite.ToposHom.comp (AlgebraicSpace.ringedToposHom (inducedHom eX eY f))
          (inclusion G Y eY)).toTopos.pushforward ≅
      (RingedSite.ToposHom.comp (inclusion F X eX) (etaleRingedToposHom f)).toTopos.pushforward :=
  isoWhiskerRight (etaleDirectImageIso eX eY f)
      ((smallEtaleFunctor G Y eY).sheafPushforwardCocontinuous (Type u)
        (AlgebraicSpace.smallEtaleTopology G) Y.etaleTopology) ≪≫
    sheafPushforwardCocontinuousComp
      (AlgebraicSpace.smallEtaleTopology F) (AlgebraicSpace.smallEtaleTopology G)
      Y.etaleTopology
      (AlgebraicSpace.etaleRestriction (inducedHom eX eY f))
      (smallEtaleFunctor G Y eY) ≪≫
      (sheafPushforwardCocontinuousComp'
          (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology Y.etaleTopology
          (smallEtaleFunctor F X eX) (toCartesianBasedFunctor f).toFunctor
          (compareInclusionFunctorIso eX eY f α)).symm

/-- The commutative square of ringed topoi with edges `f_small`, `i_F`, `i_G`, and `f`. -/
def compareInclusion :
    RingedSite.ToposHom.CommSquare
      (AlgebraicSpace.ringedSite F) (AlgebraicSpace.ringedSite G)
      (etaleRingedSite X) (etaleRingedSite Y) where
  upper := AlgebraicSpace.ringedToposHom (inducedHom eX eY f)
  left := inclusion F X eX
  right := inclusion G Y eY
  lower := etaleRingedToposHom f
  cell :=
    { homIso := compareInclusionIso eX eY f α
      comm := sorry }

/-- The four edges of `compareInclusion` are `f_small`, `i_F`, `i_G`, and `f`, and the stored
`2`-cell is `compareInclusionIso`. -/
theorem compareInclusion_spec :
    (compareInclusion eX eY f α).upper =
        AlgebraicSpace.ringedToposHom (inducedHom eX eY f) ∧
      (compareInclusion eX eY f α).left = inclusion F X eX ∧
      (compareInclusion eX eY f α).right = inclusion G Y eY ∧
      (compareInclusion eX eY f α).lower = etaleRingedToposHom f ∧
      (compareInclusion eX eY f α).cell.homIso = compareInclusionIso eX eY f α :=
  sorry

end AlgebraicGeometry.GroupoidsOver
