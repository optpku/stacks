module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.Scheme.Pushout.Thickening
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap76.Lemma_76_9_2_Thickening

/-!
# Étale presentation cubes over a pushout

A commutative cube relating a pushout `G = V ⨿_U U'` of algebraic spaces over a
thickening–affine pushout `Y' = Y ⨿_X X'` to a scheme-level pushout
`G1 = V1 ⨿_{U1} U1'`, with cartesian side faces and surjective étale northeast
arrows.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Pushout

/-- The overlap `U = U' ×_{X'} X` of a triple `(V, U', φ)`. -/
abbrev overlap {S : Scheme.{u}} {X X' U' : AlgebraicSpace S} (i : X ⟶ X') (pU' : U' ⟶ X') :
    AlgebraicSpace S :=
  pullback pU' i

/-- The projection `U ⟶ U'` of the overlap pullback. -/
abbrev toU' {S : Scheme.{u}} {X X' U' : AlgebraicSpace S} (i : X ⟶ X') (pU' : U' ⟶ X') :
    overlap i pU' ⟶ U' :=
  pullback.fst pU' i

/-- The projection `U ⟶ X` of the overlap pullback. -/
abbrev toX {S : Scheme.{u}} {X X' U' : AlgebraicSpace S} (i : X ⟶ X') (pU' : U' ⟶ X') :
    overlap i pU' ⟶ X :=
  pullback.snd pU' i

/-- The comparison `U ⟶ V` obtained by transporting the overlap along `φ`. -/
abbrev toV {S : Scheme.{u}} {X X' Y V U' : AlgebraicSpace S}
    (i : X ⟶ X') (f : X ⟶ Y) (pV : V ⟶ Y) (pU' : U' ⟶ X')
    (φ : pullback pV f ≅ pullback pU' i) : overlap i pU' ⟶ V :=
  φ.inv ≫ pullback.fst pV f

/-- The scheme-level overlap `U1 = V1 ×_Y X` represented by `f`. -/
def schemeOverlap {S : Scheme.{u}} {X Y V : AlgebraicSpace S} {V1 : Over S}
    (f : X ⟶ Y) (πV : ofOver V1 ⟶ V) (pV : V ⟶ Y)
    (hf : yoneda.relativelyRepresentable f) : Over S :=
  hf.pullback (πV ≫ pV)

/-- The scheme morphism `U1 ⟶ V1` as the representing second projection. -/
abbrev schemeOverlap_toV1 {S : Scheme.{u}} {X Y V : AlgebraicSpace S} {V1 : Over S}
    (f : X ⟶ Y) (πV : ofOver V1 ⟶ V) (pV : V ⟶ Y)
    (hf : yoneda.relativelyRepresentable f) :
    schemeOverlap f πV pV hf ⟶ V1 :=
  hf.snd (πV ≫ pV)

/-- The algebraic-space projection `ofOver U1 ⟶ X`. -/
abbrev schemeOverlap_toX {S : Scheme.{u}} {X Y V : AlgebraicSpace S} {V1 : Over S}
    (f : X ⟶ Y) (πV : ofOver V1 ⟶ V) (pV : V ⟶ Y)
    (hf : yoneda.relativelyRepresentable f) :
    ofOver (schemeOverlap f πV pV hf) ⟶ X :=
  hf.fst (πV ≫ pV)

/-- Compatibility of the representing cone `U1 ⟶ V1` and `U1 ⟶ X` with `V ⟶ Y` and `X ⟶ Y`. -/
theorem schemeOverlap_lift_w {S : Scheme.{u}} {X Y V : AlgebraicSpace S} {V1 : Over S}
    (f : X ⟶ Y) (πV : ofOver V1 ⟶ V) (pV : V ⟶ Y)
    (hf : yoneda.relativelyRepresentable f) :
    (ofOverMap (schemeOverlap_toV1 f πV pV hf) ≫ πV) ≫ pV =
      schemeOverlap_toX f πV pV hf ≫ f :=
  sorry

/-- The northeast arrow `ofOver U1 ⟶ U` induced by the representing pullback and `φ`. -/
abbrev toOverlap {S : Scheme.{u}} {X X' Y V U' : AlgebraicSpace S} {V1 : Over S}
    (i : X ⟶ X') (f : X ⟶ Y) (πV : ofOver V1 ⟶ V) (pV : V ⟶ Y) (pU' : U' ⟶ X')
    (φ : pullback pV f ≅ pullback pU' i) (hf : yoneda.relativelyRepresentable f) :
    ofOver (schemeOverlap f πV pV hf) ⟶ overlap i pU' :=
  pullback.lift (ofOverMap (schemeOverlap_toV1 f πV pV hf) ≫ πV)
      (schemeOverlap_toX f πV pV hf) (schemeOverlap_lift_w f πV pV hf) ≫
    φ.hom

/-- Compatibility of a morphism of schemes over `S` with the two structure maps, as needed to
form the scheme-level pushout over `S`. -/
theorem frontPushout_w {S : Scheme.{u}} {U1 U1' V1 : Over S} (i1 : U1 ⟶ U1') (f1 : U1 ⟶ V1) :
    i1.left ≫ U1'.hom = f1.left ≫ V1.hom :=
  sorry

/-- The scheme-level pushout `G1 = V1 ⨿_{U1} U1'` as an object of `Over S`. -/
def frontPushout {S : Scheme.{u}} {U1 U1' V1 : Over S} (i1 : U1 ⟶ U1') (f1 : U1 ⟶ V1)
    [AlgebraicGeometry.IsThickening i1.left] [IsAffineHom f1.left] : Over S :=
  Over.mk (pushout.desc U1'.hom V1.hom (frontPushout_w i1 f1))

/-- The front inclusion `U1' ⟶ G1` is the scheme-level `pushout.inl`. -/
theorem frontInl_w {S : Scheme.{u}} {U1 U1' V1 : Over S} (i1 : U1 ⟶ U1') (f1 : U1 ⟶ V1)
    [AlgebraicGeometry.IsThickening i1.left] [IsAffineHom f1.left] :
    pushout.inl i1.left f1.left ≫ (frontPushout i1 f1).hom = U1'.hom :=
  sorry

/-- The front inclusion `V1 ⟶ G1` is the scheme-level `pushout.inr`. -/
theorem frontInr_w {S : Scheme.{u}} {U1 U1' V1 : Over S} (i1 : U1 ⟶ U1') (f1 : U1 ⟶ V1)
    [AlgebraicGeometry.IsThickening i1.left] [IsAffineHom f1.left] :
    pushout.inr i1.left f1.left ≫ (frontPushout i1 f1).hom = V1.hom :=
  sorry

/-- The front right vertical arrow `U1' ⟶ G1`. -/
def frontInl {S : Scheme.{u}} {U1 U1' V1 : Over S} (i1 : U1 ⟶ U1') (f1 : U1 ⟶ V1)
    [AlgebraicGeometry.IsThickening i1.left] [IsAffineHom f1.left] :
    U1' ⟶ frontPushout i1 f1 :=
  Over.homMk (pushout.inl i1.left f1.left) (frontInl_w i1 f1)

/-- The front bottom arrow `V1 ⟶ G1`. -/
def frontInr {S : Scheme.{u}} {U1 U1' V1 : Over S} (i1 : U1 ⟶ U1') (f1 : U1 ⟶ V1)
    [AlgebraicGeometry.IsThickening i1.left] [IsAffineHom f1.left] :
    V1 ⟶ frontPushout i1 f1 :=
  Over.homMk (pushout.inr i1.left f1.left) (frontInr_w i1 f1)

/-- After `ofOverMap`, the front square is the pushout `G1 = V1 ⨿_{U1} U1'`. -/
theorem ofOver_front_isPushout {S : Scheme.{u}} {U1 U1' V1 : Over S}
    (i1 : U1 ⟶ U1') (f1 : U1 ⟶ V1)
    [AlgebraicGeometry.IsThickening i1.left] [IsAffineHom f1.left] :
    IsPushout (ofOverMap i1) (ofOverMap f1) (ofOverMap (frontInl i1 f1))
      (ofOverMap (frontInr i1 f1)) :=
  sorry

/-- Compatibility of the two paths `ofOver U1 ⟶ G`, from top-face commutativity, the
back-face pushout law, and the overlap lift. -/
def toFrontPushout_w {S : Scheme.{u}} {X X' Y V U' G : AlgebraicSpace S} {V1 U1' : Over S}
    (i : X ⟶ X') (f : X ⟶ Y) (pV : V ⟶ Y) (pU' : U' ⟶ X')
    (φ : pullback pV f ≅ pullback pU' i) (inlG : V ⟶ G) (inrG : U' ⟶ G)
    (hG : IsPushout (toU' i pU') (toV i f pV pU' φ) inrG inlG)
    (πV : ofOver V1 ⟶ V) (πU' : ofOver U1' ⟶ U') (hf : yoneda.relativelyRepresentable f)
    (i1 : schemeOverlap f πV pV hf ⟶ U1')
    (hTop : ofOverMap i1 ≫ πU' = toOverlap i f πV pV pU' φ hf ≫ toU' i pU') :
    ofOverMap i1 ≫ πU' ≫ inrG =
      ofOverMap (schemeOverlap_toV1 f πV pV hf) ≫ πV ≫ inlG :=
  let l := pullback.lift (ofOverMap (schemeOverlap_toV1 f πV pV hf) ≫ πV)
      (schemeOverlap_toX f πV pV hf) (schemeOverlap_lift_w f πV pV hf)
  let hUV : toOverlap i f πV pV pU' φ hf ≫ toV i f pV pU' φ =
      ofOverMap (schemeOverlap_toV1 f πV pV hf) ≫ πV :=
    ((Category.assoc l φ.hom (φ.inv ≫ pullback.fst pV f)).trans
      (whisker_eq l ((Category.assoc φ.hom φ.inv (pullback.fst pV f)).symm.trans
        ((eq_whisker φ.hom_inv_id (pullback.fst pV f)).trans
          (Category.id_comp (pullback.fst pV f)))))).trans
      (pullback.lift_fst (ofOverMap (schemeOverlap_toV1 f πV pV hf) ≫ πV)
        (schemeOverlap_toX f πV pV hf) (schemeOverlap_lift_w f πV pV hf))
  ((Category.assoc (ofOverMap i1) πU' inrG).symm.trans (eq_whisker hTop inrG)).trans <|
    (Category.assoc (toOverlap i f πV pV pU' φ hf) (toU' i pU') inrG).trans <|
      (whisker_eq (toOverlap i f πV pV pU' φ hf) hG.w).trans <|
        (Category.assoc (toOverlap i f πV pV pU' φ hf) (toV i f pV pU' φ) inlG).symm.trans <|
          (eq_whisker hUV inlG).trans
            (Category.assoc (ofOverMap (schemeOverlap_toV1 f πV pV hf)) πV inlG)

/-- The northeast arrow `ofOver G1 ⟶ G` by pushout descent of `πV ≫ inlG` and `πU' ≫ inrG`. -/
def toFrontPushout {S : Scheme.{u}} {X X' Y V U' G : AlgebraicSpace S} {V1 U1' : Over S}
    (i : X ⟶ X') (f : X ⟶ Y) (pV : V ⟶ Y) (pU' : U' ⟶ X')
    (φ : pullback pV f ≅ pullback pU' i) (inlG : V ⟶ G) (inrG : U' ⟶ G)
    (hG : IsPushout (toU' i pU') (toV i f pV pU' φ) inrG inlG)
    (πV : ofOver V1 ⟶ V) (πU' : ofOver U1' ⟶ U') (hf : yoneda.relativelyRepresentable f)
    (i1 : schemeOverlap f πV pV hf ⟶ U1')
    (hTop : ofOverMap i1 ≫ πU' = toOverlap i f πV pV pU' φ hf ≫ toU' i pU')
    [AlgebraicGeometry.IsThickening i1.left]
    [IsAffineHom (schemeOverlap_toV1 f πV pV hf).left] :
    ofOver (frontPushout i1 (schemeOverlap_toV1 f πV pV hf)) ⟶ G :=
  (ofOver_front_isPushout i1 (schemeOverlap_toV1 f πV pV hf)).desc (πU' ≫ inrG) (πV ≫ inlG)
    (toFrontPushout_w i f pV pU' φ inlG inrG hG πV πU' hf i1 hTop)

/-- A commutative cube with algebraic-space vertices `U = U' ×_{X'} X`, `U'`, `V`,
`G = V ⨿_U U'` over a thickening–affine pushout `Y' = Y ⨿_X X'`, and scheme vertices
`U1 = V1 ×_Y X`, `U1'`, `V1`, `G1 = V1 ⨿_{U1} U1'`. The side faces are cartesian, the
front and back faces are pushouts, and the northeast arrows are surjective étale. -/
structure OverEtaleCube {S : Scheme.{u}} {X X' Y Y' V U' G : AlgebraicSpace S}
    (i : X ⟶ X') (f : X ⟶ Y) (i' : X' ⟶ Y') (g : Y ⟶ Y')
    [IsThickening i] [Affine f] (hY' : IsPushout i f i' g)
    (pV : V ⟶ Y) (pU' : U' ⟶ X') (φ : pullback pV f ≅ pullback pU' i)
    (inlG : V ⟶ G) (inrG : U' ⟶ G)
    (hG : IsPushout (toU' i pU') (toV i f pV pU' φ) inrG inlG)
    {V1 : Over S} (πV : ofOver V1 ⟶ V) [Etale πV] [Surjective πV]
    (hf : yoneda.relativelyRepresentable f)
    {U1' : Over S} (πU' : ofOver U1' ⟶ U') [Etale πU'] [Surjective πU'] where
  /-- The chosen scheme thickening `U1 ⟶ U1'`. -/
  i1 : schemeOverlap f πV pV hf ⟶ U1'
  /-- The thickening `U1 ⟶ U1'` is a scheme thickening. -/
  isThickening_i1 : AlgebraicGeometry.IsThickening i1.left
  /-- The representing projection `U1 ⟶ V1` is affine. -/
  isAffineHom_f1 : IsAffineHom (schemeOverlap_toV1 f πV pV hf).left
  /-- The scheme vertex over `G`. -/
  G1 : Over S
  /-- The front right vertical arrow, as a morphism of schemes over `S`. -/
  i1' : U1' ⟶ G1
  /-- The front bottom arrow, as a morphism of schemes over `S`. -/
  g1 : V1 ⟶ G1
  /-- The northeast arrow from `U1` to `U`. -/
  πU : ofOver (schemeOverlap f πV pV hf) ⟶ overlap i pU'
  /-- The northeast arrow from `G1` to `G`. -/
  πG : ofOver G1 ⟶ G
  /-- The front face is a pushout after viewing schemes as algebraic spaces. -/
  isPushout_front :
    IsPushout (ofOverMap i1) (ofOverMap (schemeOverlap_toV1 f πV pV hf))
      (ofOverMap i1') (ofOverMap g1)
  /-- The top face is cartesian. -/
  isPullback_top : IsPullback (ofOverMap i1) πU πU' (toU' i pU')
  /-- The left face is cartesian. -/
  isPullback_left :
    IsPullback (ofOverMap (schemeOverlap_toV1 f πV pV hf)) πU πV (toV i f pV pU' φ)
  /-- The right face is cartesian. -/
  isPullback_right : IsPullback (ofOverMap i1') πU' πG inrG
  /-- The bottom face is cartesian. -/
  isPullback_bottom : IsPullback (ofOverMap g1) πV πG inlG
  /-- The northeast arrow `πU` is étale. -/
  etale_πU : Etale πU
  /-- The northeast arrow `πU` is surjective. -/
  surjective_πU : Surjective πU
  /-- The northeast arrow `πG` is étale. -/
  etale_πG : Etale πG
  /-- The northeast arrow `πG` is surjective. -/
  surjective_πG : Surjective πG

namespace OverEtaleCube

/-- Assemble an étale presentation cube from a triple `(V, U', φ)`, a pushout cocone
for `G = V ⨿_U U'`, a surjective étale scheme atlas `V1 ⟶ V`, and a thickening
`U1 ⟶ U1'` whose top face commutes with `U1 ⟶ U ⟶ U'`. Vertices `U`, `U1`, and
`G1` and the non-chosen arrows are the canonical pullbacks, `ofOverMap` images, and
scheme-level pushout inclusions. The top/right/bottom cartesian laws and the
surjective étaleness of `G1 ⟶ G` are part of the presentation data. -/
def ofTriple {S : Scheme.{u}} {X X' Y Y' V U' G : AlgebraicSpace S}
    (i : X ⟶ X') (f : X ⟶ Y) (i' : X' ⟶ Y') (g : Y ⟶ Y')
    [IsThickening i] [Affine f] (hY' : IsPushout i f i' g)
    (pV : V ⟶ Y) (pU' : U' ⟶ X') (φ : pullback pV f ≅ pullback pU' i)
    (inlG : V ⟶ G) (inrG : U' ⟶ G)
    (hG : IsPushout (toU' i pU') (toV i f pV pU' φ) inrG inlG)
    {V1 : Over S} (πV : ofOver V1 ⟶ V) [Etale πV] [Surjective πV]
    (hf : yoneda.relativelyRepresentable f)
    {U1' : Over S} (πU' : ofOver U1' ⟶ U') [Etale πU'] [Surjective πU']
    (i1 : schemeOverlap f πV pV hf ⟶ U1')
    (hTop : ofOverMap i1 ≫ πU' = toOverlap i f πV pV pU' φ hf ≫ toU' i pU')
    [hTh : AlgebraicGeometry.IsThickening i1.left]
    [hAff : IsAffineHom (schemeOverlap_toV1 f πV pV hf).left]
    (isPullback_top : IsPullback (ofOverMap i1) (toOverlap i f πV pV pU' φ hf) πU'
      (toU' i pU'))
    (isPullback_right : IsPullback
      (ofOverMap (frontInl i1 (schemeOverlap_toV1 f πV pV hf))) πU'
      (toFrontPushout i f pV pU' φ inlG inrG hG πV πU' hf i1 hTop) inrG)
    (isPullback_bottom : IsPullback
      (ofOverMap (frontInr i1 (schemeOverlap_toV1 f πV pV hf))) πV
      (toFrontPushout i f pV pU' φ inlG inrG hG πV πU' hf i1 hTop) inlG)
    (etale_πG : Etale (toFrontPushout i f pV pU' φ inlG inrG hG πV πU' hf i1 hTop))
    (surjective_πG : Surjective
      (toFrontPushout i f pV pU' φ inlG inrG hG πV πU' hf i1 hTop)) :
    OverEtaleCube i f i' g hY' pV pU' φ inlG inrG hG πV hf πU' where
  i1 := i1
  isThickening_i1 := hTh
  isAffineHom_f1 := hAff
  G1 := frontPushout i1 (schemeOverlap_toV1 f πV pV hf)
  i1' := frontInl i1 (schemeOverlap_toV1 f πV pV hf)
  g1 := frontInr i1 (schemeOverlap_toV1 f πV pV hf)
  πU := toOverlap i f πV pV pU' φ hf
  πG := toFrontPushout i f pV pU' φ inlG inrG hG πV πU' hf i1 hTop
  isPushout_front := ofOver_front_isPushout i1 (schemeOverlap_toV1 f πV pV hf)
  isPullback_top := isPullback_top
  isPullback_left := sorry
  isPullback_right := isPullback_right
  isPullback_bottom := isPullback_bottom
  etale_πU := sorry
  surjective_πU := sorry
  etale_πG := etale_πG
  surjective_πG := surjective_πG

variable {S : Scheme.{u}} {X X' Y Y' V U' G : AlgebraicSpace S}
variable {i : X ⟶ X'} {f : X ⟶ Y} {i' : X' ⟶ Y'} {g : Y ⟶ Y'}
variable [IsThickening i] [Affine f] {hY' : IsPushout i f i' g}
variable {pV : V ⟶ Y} {pU' : U' ⟶ X'} {φ : pullback pV f ≅ pullback pU' i}
variable {inlG : V ⟶ G} {inrG : U' ⟶ G}
variable {hG : IsPushout (toU' i pU') (toV i f pV pU' φ) inrG inlG}
variable {V1 : Over S} {πV : ofOver V1 ⟶ V} [Etale πV] [Surjective πV]
variable {hf : yoneda.relativelyRepresentable f}
variable {U1' : Over S} {πU' : ofOver U1' ⟶ U'} [Etale πU'] [Surjective πU']

/-- The northeast arrow from the scheme-level pushout `G1` to `G`. -/
abbrev toPushout (C : OverEtaleCube i f i' g hY' pV pU' φ inlG inrG hG πV hf πU') :
    ofOver C.G1 ⟶ G :=
  C.πG

/-- An étale presentation cube has pushout front and back faces, cartesian remaining
faces, and surjective étale northeast arrows. -/
theorem spec (C : OverEtaleCube i f i' g hY' pV pU' φ inlG inrG hG πV hf πU') :
    (IsPushout i f i' g ∧
      IsPushout (toU' i pU') (toV i f pV pU' φ) inrG inlG ∧
      IsPushout (ofOverMap C.i1) (ofOverMap (schemeOverlap_toV1 f πV pV hf))
        (ofOverMap C.i1') (ofOverMap C.g1)) ∧
    (IsPullback (ofOverMap C.i1) C.πU πU' (toU' i pU') ∧
      IsPullback (ofOverMap (schemeOverlap_toV1 f πV pV hf)) C.πU πV (toV i f pV pU' φ) ∧
      IsPullback (ofOverMap C.i1') πU' C.πG inrG ∧
      IsPullback (ofOverMap C.g1) πV C.πG inlG) ∧
    ((Etale C.πU ∧ Surjective C.πU) ∧ (Etale πU' ∧ Surjective πU') ∧
      (Etale πV ∧ Surjective πV) ∧ (Etale C.πG ∧ Surjective C.πG)) :=
  sorry

/-- In particular, the northeast arrow `G1 ⟶ G` is surjective étale. -/
theorem etale_toPushout
    (C : OverEtaleCube i f i' g hY' pV pU' φ inlG inrG hG πV hf πU') :
    Etale C.toPushout ∧ Surjective C.toPushout :=
  sorry

end OverEtaleCube

end AlgebraicGeometry.AlgebraicSpace.Pushout


