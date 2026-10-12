/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap66.Lemma_66_18_8_Pullback

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

/-- The underlying morphism of schemes over `S` induced by a map of small étale objects
after base change along a representable morphism. -/
noncomputable def smallEtalePullback_mapLeft {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) {V W : smallEtaleSite Y} (g : V ⟶ W) :
    hf.pullback V.hom ⟶ hf.pullback W.hom :=
  yoneda.preimage
    ((hf.isPullback W.hom).lift (hf.fst V.hom) (yoneda.map (hf.snd V.hom ≫ g.left)) sorry)

/-- Base change along a representable morphism, as a functor of small étale sites. -/
noncomputable def smallEtalePullback {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f) :
    smallEtaleSite Y ⥤ smallEtaleSite X where
  obj V := @smallEtaleSite.mk S X (hf.pullback V.hom) (hf.fst V.hom) sorry
  map g := MorphismProperty.CostructuredArrow.homMk (smallEtalePullback_mapLeft hf g)
    trivial sorry
  map_id := sorry
  map_comp := sorry

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

/-- The representing fibre product of a representable morphism is isomorphic to the chosen
fibre product in the category of algebraic spaces. -/
noncomputable def smallEtalePullback_objIso {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) (V : smallEtaleSite Y) :
    ofOver (hf.pullback V.hom) ≅ pullback V.hom f where
  hom := pullback.lift (ofOverMap (hf.snd V.hom)) (hf.fst V.hom) sorry
  inv := (hf.isPullback V.hom).lift (pullback.snd V.hom f) (pullback.fst V.hom f) sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The small étale pullback of a representable morphism compares with spaces étale pullback
under `smallEtaleInclusion`. -/
noncomputable def smallEtalePullbackCompInclusion {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f) :
    smallEtalePullback f hf ⋙ smallEtaleInclusion X ≅
      smallEtaleInclusion Y ⋙ spacesEtalePullback f :=
  NatIso.ofComponents
    (fun V ↦ MorphismProperty.Over.isoMk (smallEtalePullback_objIso hf V) sorry) sorry

/-- Componentwise, `smallEtalePullbackCompInclusion` is `smallEtalePullback_objIso`. -/
theorem smallEtalePullbackCompInclusion_app_left {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f) (V : smallEtaleSite Y) :
    ((smallEtalePullbackCompInclusion f hf).hom.app V).left =
      (smallEtalePullback_objIso hf V).hom :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
