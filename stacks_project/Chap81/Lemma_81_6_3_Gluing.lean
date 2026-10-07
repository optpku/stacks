module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap81.Lemma_81_6_2_Pushout

/-!
# Pushout gluing of algebraic spaces over a thickening–affine pushout

Base change along `Y ⟶ Y ⨿_X X'` and `X' ⟶ Y ⨿_X X'` yields a functor from algebraic
spaces over the pushout to compatible pairs over `Y` and `X'`. Pushout along the overlap
span of such a pair is left adjoint to this base change, and both functors preserve
algebraic spaces representable by schemes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.PushoutAlongThickening

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Pushout.Gluing

variable {S : Scheme.{u}} {X X' Y : AlgebraicSpace S}

/-- The base-change square from algebraic spaces over the canonical pushout to algebraic
spaces over `Y` and `X'`, whose structural isomorphism compares the two iterated
pullbacks to `X`. -/
noncomputable def square (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f] :
    CategoricalPullback.CatCommSqOver (Over.pullback f) (Over.pullback i)
      (Over (pushout i f)) where
  fst := Over.pullback (pushout.inr i f)
  snd := Over.pullback (pushout.inl i f)
  iso := (Over.pullbackComp f (pushout.inr i f)).symm ≪≫
    eqToIso (congrArg (fun k : X ⟶ pushout i f ↦ Over.pullback k)
      (pushout.condition : i ≫ pushout.inl i f = f ≫ pushout.inr i f).symm) ≪≫
    Over.pullbackComp i (pushout.inl i f)

/-- The first leg of `square i f` is base change along `Y ⟶ pushout i f`. -/
theorem square_fst (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f] :
    (square i f).fst = Over.pullback (pushout.inr i f) :=
  sorry

/-- The second leg of `square i f` is base change along `X' ⟶ pushout i f`. -/
theorem square_snd (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f] :
    (square i f).snd = Over.pullback (pushout.inl i f) :=
  sorry

/-- Base change from algebraic spaces over the canonical pushout to compatible algebraic
spaces over `Y` and `X'`. -/
abbrev baseChange (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f] :
    Over (pushout i f) ⥤ CategoricalPullback (Over.pullback f) (Over.pullback i) :=
  (square i f).comparison

/-- The first component of base change is pullback along `Y ⟶ pushout i f`. -/
theorem baseChange_obj_fst (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    (Z : Over (pushout i f)) :
    ((baseChange i f).obj Z).fst = (Over.pullback (pushout.inr i f)).obj Z :=
  sorry

/-- The second component of base change is pullback along `X' ⟶ pushout i f`. -/
theorem baseChange_obj_snd (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    (Z : Over (pushout i f)) :
    ((baseChange i f).obj Z).snd = (Over.pullback (pushout.inl i f)).obj Z :=
  sorry

/-- The first component of base change of a scheme over the pushout is a scheme. -/
instance baseChange_fst_isScheme (i : X ⟶ X') (f : X ⟶ Y)
    [IsThickening i] [Affine f] (Z : Over (pushout i f)) [IsScheme Z.left] :
    IsScheme ((baseChange i f).obj Z).fst.left :=
  sorry

/-- The second component of base change of a scheme over the pushout is a scheme. -/
instance baseChange_snd_isScheme (i : X ⟶ X') (f : X ⟶ Y)
    [IsThickening i] [Affine f] (Z : Over (pushout i f)) [IsScheme Z.left] :
    IsScheme ((baseChange i f).obj Z).snd.left :=
  sorry

/-- The overlap underlying a compatible pair is the selected pullback `P.fst.left ×_Y X`. -/
abbrev overlap (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    (P : CategoricalPullback (Over.pullback f) (Over.pullback i)) : AlgebraicSpace S :=
  ((Over.pullback f).obj P.fst).left

/-- The overlap is the selected pullback of `P.fst.hom` and `f`. -/
theorem overlap_def (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    (P : CategoricalPullback (Over.pullback f) (Over.pullback i)) :
    overlap i f P = pullback P.fst.hom f :=
  sorry

/-- The projection from the overlap to the algebraic space over `Y`. -/
abbrev toFst (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    (P : CategoricalPullback (Over.pullback f) (Over.pullback i)) :
    overlap i f P ⟶ P.fst.left :=
  pullback.fst P.fst.hom f

/-- The first overlap projection is the selected pullback projection. -/
theorem toFst_def (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    (P : CategoricalPullback (Over.pullback f) (Over.pullback i)) :
    toFst i f P = pullback.fst P.fst.hom f :=
  sorry

/-- The projection from the overlap to the algebraic space over `X'`, transported through
the structural isomorphism of the compatible pair. -/
def toSnd (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    (P : CategoricalPullback (Over.pullback f) (Over.pullback i)) :
    overlap i f P ⟶ P.snd.left :=
  P.iso.hom.left ≫ pullback.fst P.snd.hom i

/-- The second overlap projection is transport through `P.iso` followed by a pullback
projection. -/
theorem toSnd_def (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    (P : CategoricalPullback (Over.pullback f) (Over.pullback i)) :
    toSnd i f P = P.iso.hom.left ≫ pullback.fst P.snd.hom i :=
  sorry

/-- The first overlap projection is affine. -/
instance toFst_affine (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    (P : CategoricalPullback (Over.pullback f) (Over.pullback i)) :
    Affine (toFst i f P) :=
  sorry

/-- The second overlap projection is a thickening. -/
instance toSnd_isThickening (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    (P : CategoricalPullback (Over.pullback f) (Over.pullback i)) :
    IsThickening (toSnd i f P) :=
  sorry

/-- The overlap span of a compatible pair has the canonical algebraic-space pushout. -/
instance hasPushout (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    (P : CategoricalPullback (Over.pullback f) (Over.pullback i)) :
    HasPushout (toSnd i f P) (toFst i f P) :=
  inferInstance

/-- The selected pushout of the overlap span of a compatible pair. -/
noncomputable def gluedPushout (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    (P : CategoricalPullback (Over.pullback f) (Over.pullback i)) : AlgebraicSpace S :=
  pushout (toSnd i f P) (toFst i f P)

/-- The coprojection from the component over `X'` into the selected glued pushout. -/
noncomputable def gluedInl (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    (P : CategoricalPullback (Over.pullback f) (Over.pullback i)) :
    P.snd.left ⟶ gluedPushout i f P :=
  pushout.inl (toSnd i f P) (toFst i f P)

/-- The coprojection from the component over `Y` into the selected glued pushout. -/
noncomputable def gluedInr (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    (P : CategoricalPullback (Over.pullback f) (Over.pullback i)) :
    P.fst.left ⟶ gluedPushout i f P :=
  pushout.inr (toSnd i f P) (toFst i f P)

/-- The maps from the two components of a compatible pair to `pushout i f` agree on their
overlap. -/
theorem mapToPushout_condition (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    (P : CategoricalPullback (Over.pullback f) (Over.pullback i)) :
    toSnd i f P ≫ P.snd.hom ≫ pushout.inl i f =
      toFst i f P ≫ P.fst.hom ≫ pushout.inr i f :=
  sorry

/-- The structure morphism from the pushout glued from `P` to the canonical pushout of `i`
and `f`. -/
noncomputable def mapToPushout (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    (P : CategoricalPullback (Over.pullback f) (Over.pullback i)) :
    gluedPushout i f P ⟶ pushout i f :=
  pushout.desc (P.snd.hom ≫ pushout.inl i f) (P.fst.hom ≫ pushout.inr i f)
    (mapToPushout_condition i f P)

/-- The structure morphism restricts on the `P.snd` component to its given map to `X'`. -/
theorem mapToPushout_inl (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    (P : CategoricalPullback (Over.pullback f) (Over.pullback i)) :
    gluedInl i f P ≫ mapToPushout i f P = P.snd.hom ≫ pushout.inl i f :=
  sorry

/-- The structure morphism restricts on the `P.fst` component to its given map to `Y`. -/
theorem mapToPushout_inr (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    (P : CategoricalPullback (Over.pullback f) (Over.pullback i)) :
    gluedInr i f P ≫ mapToPushout i f P = P.fst.hom ≫ pushout.inr i f :=
  sorry

/-- The algebraic space over `pushout i f` obtained by gluing a compatible pair along its
overlap. -/
noncomputable def gluedObject (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    (P : CategoricalPullback (Over.pullback f) (Over.pullback i)) : Over (pushout i f) :=
  Over.mk (mapToPushout i f P)

/-- The underlying algebraic space of `gluedObject i f P` is the selected overlap pushout. -/
theorem gluedObject_left (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    (P : CategoricalPullback (Over.pullback f) (Over.pullback i)) :
    (gluedObject i f P).left = gluedPushout i f P :=
  sorry

/-- The map on overlaps induced by a morphism of compatible pairs. -/
abbrev overlapMap (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    {P Q : CategoricalPullback (Over.pullback f) (Over.pullback i)} (k : P ⟶ Q) :
    overlap i f P ⟶ overlap i f Q :=
  ((Over.pullback f).map k.fst).left

/-- The overlap map is the underlying map produced by base change from `k.fst`. -/
theorem overlapMap_def (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    {P Q : CategoricalPullback (Over.pullback f) (Over.pullback i)} (k : P ⟶ Q) :
    overlapMap i f k = ((Over.pullback f).map k.fst).left :=
  sorry

/-- The overlap map commutes with the first overlap projections. -/
theorem toFst_naturality (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    {P Q : CategoricalPullback (Over.pullback f) (Over.pullback i)} (k : P ⟶ Q) :
    toFst i f P ≫ k.fst.left = overlapMap i f k ≫ toFst i f Q :=
  sorry

/-- The overlap map commutes with the second overlap projections. -/
theorem toSnd_naturality (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    {P Q : CategoricalPullback (Over.pullback f) (Over.pullback i)} (k : P ⟶ Q) :
    toSnd i f P ≫ k.snd.left = overlapMap i f k ≫ toSnd i f Q :=
  sorry

/-- The underlying morphism between glued pushouts induced by a morphism of compatible
pairs. -/
noncomputable def gluedMapUnderlying (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    {P Q : CategoricalPullback (Over.pullback f) (Over.pullback i)} (k : P ⟶ Q) :
    (gluedObject i f P).left ⟶ (gluedObject i f Q).left :=
  pushout.map (toSnd i f P) (toFst i f P) (toSnd i f Q) (toFst i f Q)
    k.snd.left k.fst.left (overlapMap i f k) (toSnd_naturality i f k) (toFst_naturality i f k)

/-- The glued underlying morphism commutes with the structure maps to `pushout i f`. -/
theorem gluedMapUnderlying_over (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    {P Q : CategoricalPullback (Over.pullback f) (Over.pullback i)} (k : P ⟶ Q) :
    gluedMapUnderlying i f k ≫ mapToPushout i f Q = mapToPushout i f P :=
  sorry

/-- The morphism of algebraic spaces over `pushout i f` induced by a morphism of compatible
pairs. -/
noncomputable def glueMap (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    {P Q : CategoricalPullback (Over.pullback f) (Over.pullback i)} (k : P ⟶ Q) :
    gluedObject i f P ⟶ gluedObject i f Q :=
  Over.homMk (gluedMapUnderlying i f k) (gluedMapUnderlying_over i f k)

/-- The underlying map of `glueMap i f k` is the canonical map between the selected
pushouts. -/
theorem glueMap_left (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    {P Q : CategoricalPullback (Over.pullback f) (Over.pullback i)} (k : P ⟶ Q) :
    (glueMap i f k).left = gluedMapUnderlying i f k :=
  sorry

/-- The glued map attached to an identity morphism is an identity. -/
theorem glueMap_id (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    (P : CategoricalPullback (Over.pullback f) (Over.pullback i)) :
    glueMap i f (𝟙 P) = 𝟙 (gluedObject i f P) :=
  sorry

/-- Glued maps preserve composition. -/
theorem glueMap_comp (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    {P Q R : CategoricalPullback (Over.pullback f) (Over.pullback i)}
    (k : P ⟶ Q) (l : Q ⟶ R) :
    glueMap i f (k ≫ l) = glueMap i f k ≫ glueMap i f l :=
  sorry

/-- The pushout gluing functor from compatible algebraic spaces over `Y` and `X'` to
algebraic spaces over the canonical pushout. -/
noncomputable def glue (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f] :
    CategoricalPullback (Over.pullback f) (Over.pullback i) ⥤ Over (pushout i f) where
  obj := gluedObject i f
  map := glueMap i f
  map_id := glueMap_id i f
  map_comp := glueMap_comp i f

/-- On objects, `glue i f` has the selected overlap pushout as underlying algebraic space. -/
theorem glue_obj_left (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    (P : CategoricalPullback (Over.pullback f) (Over.pullback i)) :
    ((glue i f).obj P).left = gluedPushout i f P :=
  sorry

/-- The pushout glued from a compatible pair of schemes is a scheme. -/
instance glue_isScheme (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    (P : CategoricalPullback (Over.pullback f) (Over.pullback i))
    [IsScheme P.fst.left] [IsScheme P.snd.left] :
    IsScheme ((glue i f).obj P).left :=
  sorry

/-- The pullback-lift equation used by the first component of `toBaseChange`. -/
theorem toBaseChangeFst_condition (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    {P : CategoricalPullback (Over.pullback f) (Over.pullback i)}
    {Z : Over (pushout i f)} (k : (glue i f).obj P ⟶ Z) :
    (gluedInr i f P ≫ k.left) ≫ Z.hom = P.fst.hom ≫ pushout.inr i f :=
  sorry

/-- The first pullback lift is a morphism over `Y`. -/
theorem toBaseChangeFst_over (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    {P : CategoricalPullback (Over.pullback f) (Over.pullback i)}
    {Z : Over (pushout i f)} (k : (glue i f).obj P ⟶ Z) :
    pullback.lift (gluedInr i f P ≫ k.left) P.fst.hom (toBaseChangeFst_condition i f k) ≫
        pullback.snd Z.hom (pushout.inr i f) =
      P.fst.hom :=
  sorry

/-- The first component of the adjunction map into base change. -/
noncomputable def toBaseChangeFst (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    {P : CategoricalPullback (Over.pullback f) (Over.pullback i)}
    {Z : Over (pushout i f)} (k : (glue i f).obj P ⟶ Z) :
    P.fst ⟶ ((baseChange i f).obj Z).fst :=
  Over.homMk
    (pullback.lift (gluedInr i f P ≫ k.left) P.fst.hom (toBaseChangeFst_condition i f k))
    (toBaseChangeFst_over i f k)

/-- The pullback-lift equation used by the second component of `toBaseChange`. -/
theorem toBaseChangeSnd_condition (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    {P : CategoricalPullback (Over.pullback f) (Over.pullback i)}
    {Z : Over (pushout i f)} (k : (glue i f).obj P ⟶ Z) :
    (gluedInl i f P ≫ k.left) ≫ Z.hom = P.snd.hom ≫ pushout.inl i f :=
  sorry

/-- The second pullback lift is a morphism over `X'`. -/
theorem toBaseChangeSnd_over (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    {P : CategoricalPullback (Over.pullback f) (Over.pullback i)}
    {Z : Over (pushout i f)} (k : (glue i f).obj P ⟶ Z) :
    pullback.lift (gluedInl i f P ≫ k.left) P.snd.hom (toBaseChangeSnd_condition i f k) ≫
        pullback.snd Z.hom (pushout.inl i f) =
      P.snd.hom :=
  sorry

/-- The second component of the adjunction map into base change. -/
noncomputable def toBaseChangeSnd (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    {P : CategoricalPullback (Over.pullback f) (Over.pullback i)}
    {Z : Over (pushout i f)} (k : (glue i f).obj P ⟶ Z) :
    P.snd ⟶ ((baseChange i f).obj Z).snd :=
  Over.homMk
    (pullback.lift (gluedInl i f P ≫ k.left) P.snd.hom (toBaseChangeSnd_condition i f k))
    (toBaseChangeSnd_over i f k)

/-- The two components of the adjunction map satisfy the categorical-pullback compatibility
condition. -/
theorem toBaseChange_w (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    {P : CategoricalPullback (Over.pullback f) (Over.pullback i)}
    {Z : Over (pushout i f)} (k : (glue i f).obj P ⟶ Z) :
    (Over.pullback f).map (toBaseChangeFst i f k) ≫ ((baseChange i f).obj Z).iso.hom =
      P.iso.hom ≫ (Over.pullback i).map (toBaseChangeSnd i f k) :=
  sorry

/-- A morphism from a glued object to `Z` gives a compatible pair of morphisms into the two
base changes of `Z`. -/
noncomputable def toBaseChange (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    {P : CategoricalPullback (Over.pullback f) (Over.pullback i)}
    {Z : Over (pushout i f)} (k : (glue i f).obj P ⟶ Z) :
    P ⟶ (baseChange i f).obj Z where
  fst := toBaseChangeFst i f k
  snd := toBaseChangeSnd i f k
  w := toBaseChange_w i f k

/-- The first projection of `toBaseChange i f k` is its canonical pullback lift. -/
theorem toBaseChange_fst (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    {P : CategoricalPullback (Over.pullback f) (Over.pullback i)}
    {Z : Over (pushout i f)} (k : (glue i f).obj P ⟶ Z) :
    (toBaseChange i f k).fst = toBaseChangeFst i f k :=
  sorry

/-- The maps induced from a compatible pair to the two pullbacks of `Z` agree on the
overlap. -/
theorem fromBaseChange_condition (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    {P : CategoricalPullback (Over.pullback f) (Over.pullback i)}
    {Z : Over (pushout i f)} (k : P ⟶ (baseChange i f).obj Z) :
    toSnd i f P ≫ k.snd.left ≫ pullback.fst Z.hom (pushout.inl i f) =
      toFst i f P ≫ k.fst.left ≫ pullback.fst Z.hom (pushout.inr i f) :=
  sorry

/-- The underlying map from a glued pushout obtained from a morphism into the base-change
pair. -/
noncomputable def fromBaseChangeUnderlying (i : X ⟶ X') (f : X ⟶ Y)
    [IsThickening i] [Affine f]
    {P : CategoricalPullback (Over.pullback f) (Over.pullback i)}
    {Z : Over (pushout i f)} (k : P ⟶ (baseChange i f).obj Z) :
    ((glue i f).obj P).left ⟶ Z.left :=
  pushout.desc (k.snd.left ≫ pullback.fst Z.hom (pushout.inl i f))
    (k.fst.left ≫ pullback.fst Z.hom (pushout.inr i f)) (fromBaseChange_condition i f k)

/-- The map out of the glued pushout lies over `pushout i f`. -/
theorem fromBaseChange_over (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    {P : CategoricalPullback (Over.pullback f) (Over.pullback i)}
    {Z : Over (pushout i f)} (k : P ⟶ (baseChange i f).obj Z) :
    fromBaseChangeUnderlying i f k ≫ Z.hom = mapToPushout i f P :=
  sorry

/-- A compatible pair of morphisms into the base changes of `Z` descends to a morphism from
the glued pushout to `Z`. -/
noncomputable def fromBaseChange (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    {P : CategoricalPullback (Over.pullback f) (Over.pullback i)}
    {Z : Over (pushout i f)} (k : P ⟶ (baseChange i f).obj Z) :
    (glue i f).obj P ⟶ Z :=
  Over.homMk (fromBaseChangeUnderlying i f k) (fromBaseChange_over i f k)

/-- The underlying map of `fromBaseChange i f k` is the map induced by pushout descent. -/
theorem fromBaseChange_left (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    {P : CategoricalPullback (Over.pullback f) (Over.pullback i)}
    {Z : Over (pushout i f)} (k : P ⟶ (baseChange i f).obj Z) :
    (fromBaseChange i f k).left = fromBaseChangeUnderlying i f k :=
  sorry

/-- Descending a morphism after pulling it back recovers the original morphism. -/
theorem fromToBaseChange (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    {P : CategoricalPullback (Over.pullback f) (Over.pullback i)}
    {Z : Over (pushout i f)} (k : (glue i f).obj P ⟶ Z) :
    fromBaseChange i f (toBaseChange i f k) = k :=
  sorry

/-- Pulling back a descended compatible pair recovers the original pair. -/
theorem toFromBaseChange (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    {P : CategoricalPullback (Over.pullback f) (Over.pullback i)}
    {Z : Over (pushout i f)} (k : P ⟶ (baseChange i f).obj Z) :
    toBaseChange i f (fromBaseChange i f k) = k :=
  sorry

/-- The pushout universal property identifies maps out of a glued object with compatible
maps into the two base changes. -/
noncomputable def homEquiv (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    (P : CategoricalPullback (Over.pullback f) (Over.pullback i))
    (Z : Over (pushout i f)) :
    ((glue i f).obj P ⟶ Z) ≃ (P ⟶ (baseChange i f).obj Z) where
  toFun := toBaseChange i f
  invFun := fromBaseChange i f
  left_inv := fromToBaseChange i f
  right_inv := toFromBaseChange i f

/-- The forward action of `homEquiv` is the canonical pair of pullback lifts. -/
theorem homEquiv_apply (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    (P : CategoricalPullback (Over.pullback f) (Over.pullback i))
    (Z : Over (pushout i f)) (k : (glue i f).obj P ⟶ Z) :
    homEquiv i f P Z k = toBaseChange i f k :=
  sorry

/-- Naturality of `homEquiv` in the compatible-pair variable, in inverse form. -/
theorem homEquiv_naturality_left_symm (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    {P' P : CategoricalPullback (Over.pullback f) (Over.pullback i)}
    {Z : Over (pushout i f)} (k : P' ⟶ P) (l : P ⟶ (baseChange i f).obj Z) :
    fromBaseChange i f (k ≫ l) = (glue i f).map k ≫ fromBaseChange i f l :=
  sorry

/-- Naturality of `homEquiv` in the algebraic-space-over-the-pushout variable. -/
theorem homEquiv_naturality_right (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    {P : CategoricalPullback (Over.pullback f) (Over.pullback i)}
    {Z Z' : Over (pushout i f)} (k : (glue i f).obj P ⟶ Z) (l : Z ⟶ Z') :
    toBaseChange i f (k ≫ l) = toBaseChange i f k ≫ (baseChange i f).map l :=
  sorry

/-- The natural hom-set equivalence underlying the gluing adjunction. -/
noncomputable def coreHomEquiv (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f] :
    Adjunction.CoreHomEquiv (glue i f) (baseChange i f) where
  homEquiv := homEquiv i f
  homEquiv_naturality_left_symm := homEquiv_naturality_left_symm i f
  homEquiv_naturality_right := homEquiv_naturality_right i f

/-- The hom-set equivalence of `coreHomEquiv` is the pushout/base-change equivalence. -/
theorem coreHomEquiv_homEquiv (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f] :
    (coreHomEquiv i f).homEquiv = homEquiv i f :=
  sorry

/-- The pushout gluing functor is left adjoint to base change. -/
noncomputable def adjunction (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f] :
    glue i f ⊣ baseChange i f :=
  Adjunction.mkOfHomEquiv (coreHomEquiv i f)

/-- The hom-set equivalence of the gluing adjunction is the explicit pushout/base-change
equivalence. -/
theorem adjunction_homEquiv (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    (P : CategoricalPullback (Over.pullback f) (Over.pullback i))
    (Z : Over (pushout i f)) :
    (adjunction i f).homEquiv P Z = homEquiv i f P Z :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Pushout.Gluing
