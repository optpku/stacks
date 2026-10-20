module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SpacesPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SpacesTopos

/-!
# Small étale pullback along representable morphisms

If `f : X ⟶ Y` is a representable morphism of algebraic spaces, the functor `V ↦ X ×_Y V`
restricts to a morphism of small étale sites.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open Functor.relativelyRepresentable

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The projections defining base change of a chart morphism satisfy the pullback equation. -/
private lemma smallEtalePullback_mapLeft_condition {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) {V W : smallEtaleSite Y} (g : V ⟶ W) :
    hf.fst V.hom ≫ f = yoneda.map (hf.snd V.hom ≫ g.left) ≫ W.hom :=
  sorry

/-- The underlying morphism of schemes over `S` induced by a map of small étale objects
after base change along a representable morphism. -/
noncomputable def smallEtalePullback_mapLeft {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) {V W : smallEtaleSite Y} (g : V ⟶ W) :
    hf.pullback V.hom ⟶ hf.pullback W.hom :=
  yoneda.preimage
    ((hf.isPullback W.hom).lift (hf.fst V.hom) (yoneda.map (hf.snd V.hom ≫ g.left))
      (by exact smallEtalePullback_mapLeft_condition hf g))

/-- The representing projection obtained by base change of an étale chart is étale. -/
private lemma smallEtalePullback_obj_etale {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) (V : smallEtaleSite Y) :
    Etale (X := ofOver (hf.pullback V.hom)) (Y := X) (hf.fst V.hom) :=
  sorry

/-- The scheme arrow induced by base change commutes with the structural projections. -/
private lemma smallEtalePullback_map_w {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) {V W : smallEtaleSite Y} (g : V ⟶ W) :
    (ofOverFunctor S).map (smallEtalePullback_mapLeft hf g) ≫ hf.fst W.hom = hf.fst V.hom :=
  sorry

/-- Base change of the identity chart arrow is the identity scheme arrow. -/
private lemma smallEtalePullback_map_id {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) (V : smallEtaleSite Y) :
    smallEtalePullback_mapLeft hf (𝟙 V) = 𝟙 (hf.pullback V.hom) :=
  sorry

/-- Base change of a composite chart arrow is the composite of the induced scheme arrows. -/
private lemma smallEtalePullback_map_comp {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) {U V W : smallEtaleSite Y}
    (g : U ⟶ V) (h : V ⟶ W) :
    smallEtalePullback_mapLeft hf (g ≫ h) =
      smallEtalePullback_mapLeft hf g ≫ smallEtalePullback_mapLeft hf h :=
  sorry

/-- Base change along a representable morphism, as a functor of small étale sites. -/
noncomputable def smallEtalePullback {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f) :
    smallEtaleSite Y ⥤ smallEtaleSite X where
  obj V := smallEtaleSite.mk (U := hf.pullback V.hom) (X := X) (hf.fst V.hom) (by exact smallEtalePullback_obj_etale hf V)
  map g := MorphismProperty.CostructuredArrow.homMk (smallEtalePullback_mapLeft hf g)
    trivial (by exact smallEtalePullback_map_w hf g)
  map_id V := MorphismProperty.CostructuredArrow.Hom.ext (by exact smallEtalePullback_map_id hf V)
  map_comp g h := MorphismProperty.CostructuredArrow.Hom.ext
    (by exact smallEtalePullback_map_comp hf g h)

/-- The underlying scheme over `S` of `smallEtalePullback f hf` on `V` is the representing
fibre product. -/
@[simp]
theorem smallEtalePullback_obj_left {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f) (V : smallEtaleSite Y) :
    ((smallEtalePullback f hf).obj V).left = hf.pullback V.hom :=
  rfl

/-- The structural morphism of `smallEtalePullback f hf` on `V` is the representing projection
`hf.fst V.hom`. -/
@[simp]
theorem smallEtalePullback_obj_hom {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f) (V : smallEtaleSite Y) :
    ((smallEtalePullback f hf).obj V).hom = hf.fst V.hom :=
  rfl

/-- The morphism map of `smallEtalePullback f hf` has underlying arrow
`smallEtalePullback_mapLeft hf g`. -/
theorem smallEtalePullback_map {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f) {V W : smallEtaleSite Y} (g : V ⟶ W) :
    ((smallEtalePullback f hf).map g).left = smallEtalePullback_mapLeft hf g :=
  rfl

/-- The opposite of `smallEtalePullback f hf` has left Kan extensions on presheaves of types. -/
instance smallEtalePullback_op_hasLeftKanExtension {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) (P : (smallEtaleSite Y)ᵒᵖ ⥤ Type (u + 1)) :
    (smallEtalePullback f hf).op.HasLeftKanExtension P :=
  sorry

/-- Base change along a representable morphism is continuous for the small étale topologies. -/
instance smallEtalePullback_isContinuous {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f) :
    (smallEtalePullback f hf).IsContinuous (smallEtaleTopology Y) (smallEtaleTopology X) :=
  sorry

/-- Sheaf pullback along `smallEtalePullback f hf` preserves finite limits. -/
instance smallEtalePullback_sheafPullback_preservesFiniteLimits {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f) :
    PreservesFiniteLimits
      ((smallEtalePullback f hf).sheafPullback (Type (u + 1))
        (smallEtaleTopology Y) (smallEtaleTopology X)) :=
  sorry

/-- Base change along a representable morphism is a morphism of small étale sites. -/
instance smallEtalePullback_isMorphismOfSites {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f) :
    IsMorphismOfSites (smallEtaleTopology Y) (smallEtaleTopology X)
      (smallEtalePullback f hf) :=
  sorry

/-- The representing projections satisfy the equation for a lift into the chosen pullback. -/
private lemma smallEtalePullback_objIso_hom_condition {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) (V : smallEtaleSite Y) :
    ofOverMap (hf.snd V.hom) ≫ V.hom = hf.fst V.hom ≫ f :=
  sorry

/-- The chosen pullback projections satisfy the equation for a lift into the representing
pullback. -/
private lemma smallEtalePullback_objIso_inv_condition {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) (V : smallEtaleSite Y) :
    pullback.snd V.hom f ≫ f = pullback.fst V.hom f ≫ V.hom :=
  sorry

/-- The canonical arrow from the representing fibre product to the chosen fibre product. -/
private noncomputable def smallEtalePullback_objIsoHom {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) (V : smallEtaleSite Y) :
    ofOver (hf.pullback V.hom) ⟶ pullback V.hom f :=
  pullback.lift (ofOverMap (hf.snd V.hom)) (hf.fst V.hom)
    (smallEtalePullback_objIso_hom_condition hf V)

/-- The canonical arrow from the chosen fibre product to the representing fibre product. -/
private noncomputable def smallEtalePullback_objIsoInv {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) (V : smallEtaleSite Y) :
    pullback V.hom f ⟶ ofOver (hf.pullback V.hom) :=
  (hf.isPullback V.hom).lift (pullback.snd V.hom f) (pullback.fst V.hom f)
    (smallEtalePullback_objIso_inv_condition hf V)

/-- The comparison followed by its reverse is the identity of the representing fibre product. -/
private lemma smallEtalePullback_objIso_hom_inv_id {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) (V : smallEtaleSite Y) :
    smallEtalePullback_objIsoHom hf V ≫ smallEtalePullback_objIsoInv hf V = 𝟙 _ :=
  sorry

/-- The reverse comparison followed by the comparison is the identity of the chosen pullback. -/
private lemma smallEtalePullback_objIso_inv_hom_id {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) (V : smallEtaleSite Y) :
    smallEtalePullback_objIsoInv hf V ≫ smallEtalePullback_objIsoHom hf V = 𝟙 _ :=
  sorry

/-- The representing fibre product of a representable morphism is isomorphic to the chosen
fibre product in the category of algebraic spaces. -/
noncomputable def smallEtalePullback_objIso {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) (V : smallEtaleSite Y) :
    ofOver (hf.pullback V.hom) ≅ pullback V.hom f where
  hom := pullback.lift (ofOverMap (hf.snd V.hom)) (hf.fst V.hom)
    (by exact smallEtalePullback_objIso_hom_condition hf V)
  inv := (hf.isPullback V.hom).lift (pullback.snd V.hom f) (pullback.fst V.hom f)
    (by exact smallEtalePullback_objIso_inv_condition hf V)
  hom_inv_id := by exact smallEtalePullback_objIso_hom_inv_id hf V
  inv_hom_id := by exact smallEtalePullback_objIso_inv_hom_id hf V

/-- The fibre product comparison commutes with the projections to the base changed space. -/
private lemma smallEtalePullbackCompInclusion_w {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) (V : smallEtaleSite Y) :
    (smallEtalePullback_objIso hf V).hom ≫ pullback.snd V.hom f = hf.fst V.hom :=
  sorry

/-- The fibre product comparisons commute with base change of chart arrows. -/
private lemma smallEtalePullbackCompInclusion_naturality {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f)
    {V W : smallEtaleSite Y} (g : V ⟶ W) :
    (smallEtalePullback f hf ⋙ smallEtaleToSpaces X).map g ≫
        (MorphismProperty.Over.isoMk (smallEtalePullback_objIso hf W)
          (smallEtalePullbackCompInclusion_w hf W)).hom =
      (MorphismProperty.Over.isoMk (smallEtalePullback_objIso hf V)
          (smallEtalePullbackCompInclusion_w hf V)).hom ≫
        (smallEtaleToSpaces Y ⋙ spacesEtalePullback f).map g :=
  sorry

/-- The small étale pullback of a representable morphism compares with spaces étale pullback
under `smallEtaleToSpaces`. -/
noncomputable def smallEtalePullbackCompInclusion {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f) :
    smallEtalePullback f hf ⋙ smallEtaleToSpaces X ≅
      smallEtaleToSpaces Y ⋙ spacesEtalePullback f :=
  NatIso.ofComponents
    (fun V ↦ MorphismProperty.Over.isoMk (smallEtalePullback_objIso hf V)
      (by exact smallEtalePullbackCompInclusion_w hf V))
    (fun g ↦ by exact smallEtalePullbackCompInclusion_naturality f hf g)

/-- Componentwise, `smallEtalePullbackCompInclusion` is `smallEtalePullback_objIso`. -/
theorem smallEtalePullbackCompInclusion_app_left {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f) (V : smallEtaleSite Y) :
    ((smallEtalePullbackCompInclusion f hf).hom.app V).left =
      (smallEtalePullback_objIso hf V).hom :=
  rfl

/-- For a representable morphism, the direct image on small étale topoi is the continuous
sheaf pushforward along the representing base-change functor. -/
noncomputable def smallEtaleMorphismOfTopoiRepresentablePushforwardIso
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f) :
    (smallEtaleMorphismOfTopoi f).pushforward ≅
      (smallEtalePullback f hf).sheafPushforwardContinuous (Type (u + 1))
        (smallEtaleTopology Y) (smallEtaleTopology X) :=
  let p := (smallEtalePullback f hf).sheafPushforwardContinuous (Type (u + 1))
    (smallEtaleTopology Y) (smallEtaleTopology X)
  let e := smallEtalePresentationExtension X
  let r := smallEtalePresentationRestriction X
  let square :
      r ⋙ p ≅
        (spacesEtalePullback f).sheafPushforwardContinuous (Type (u + 1))
            (spacesEtaleTopology Y) (spacesEtaleTopology X) ⋙
          smallEtalePresentationRestriction Y :=
    @Functor.sheafPushforwardContinuousComp' _ _ _ _ _ _ _ _ _
        (smallEtalePullbackCompInclusion f hf) (Type (u + 1)) _
        (smallEtaleTopology Y) (smallEtaleTopology X) (spacesEtaleTopology X)
        inferInstance inferInstance
        (Functor.isContinuous_comp (smallEtaleToSpaces Y) (spacesEtalePullback f)
          (smallEtaleTopology Y) (spacesEtaleTopology Y) (spacesEtaleTopology X)) ≪≫
      (Functor.sheafPushforwardContinuousComp (smallEtaleToSpaces Y)
        (spacesEtalePullback f) (Type (u + 1)) (smallEtaleTopology Y)
        (spacesEtaleTopology Y) (spacesEtaleTopology X)).symm
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft e square.symm ≪≫
    (Functor.associator e r p).symm ≪≫
    Functor.isoWhiskerRight (smallEtalePresentationCounitIso X) p ≪≫
    Functor.leftUnitor p

/-- For a representable morphism, the inverse image on small étale topoi is sheaf pullback
along the representing base-change functor. -/
noncomputable def smallEtaleMorphismOfTopoiRepresentableInverseImageIso
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f) :
    (smallEtaleMorphismOfTopoi f).inverseImage ≅
      (smallEtalePullback f hf).sheafPullback (Type (u + 1))
        (smallEtaleTopology Y) (smallEtaleTopology X) :=
  Adjunction.leftAdjointUniq
    ((smallEtaleMorphismOfTopoi f).adjunction.ofNatIsoRight
      (smallEtaleMorphismOfTopoiRepresentablePushforwardIso f hf))
    ((smallEtalePullback f hf).sheafAdjunctionContinuous (Type (u + 1))
      (smallEtaleTopology Y) (smallEtaleTopology X))

end AlgebraicGeometry.AlgebraicSpace
