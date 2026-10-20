module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsoluteTransformations.Maps.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.Functoriality.Construction
public import ReasLib.CategoryTheory.Inertia.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Inertia.Presentation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Presentation

/-!
# Stabilizer square of a presentation of an algebraic stack

A presentation `P : [U/R] ⟶ X` determines a 2-commutative square in
`GroupoidsOver S` with vertices `𝒮_G`, `𝒮_U`, `I_X`, and `X`, where `G/U` is
the stabilizer group algebraic space of the presenting groupoid.
-/

@[expose] public section

-- Public constructions retain private pointwise definitions and compatibility proofs.
-- This visibility option exposes their explicit formulas without making those details public API.
set_option backward.privateInPublic true

open CategoryTheory AlgebraicGeometry AlgebraicSpace Opposite
open AlgebraicGeometry.AlgebraicStack GroupoidAlgebraicSpace
open Bicategory
open FiberedCategoryOver.Groupoids
open FiberedCategoryOver.Groupoids.Inertia
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Inertia

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] (P : Presentation X)

/-- The stabilizer group algebraic space `G` of the presenting groupoid of `P`. -/
def stabilizerSpace : AlgebraicSpace S :=
  (inertiaPresentation P.groupoid).U.left

/-- The stabilizer of a presentation is the object space of the inertia presentation of
the presenting groupoid. -/
@[simp]
theorem stabilizerSpace_eq :
    stabilizerSpace P = (inertiaPresentation P.groupoid).U.left :=
  rfl

/-- The structure morphism `G ⟶ U` of the stabilizer, as a morphism of algebraic spaces. -/
def stabilizerStructure : stabilizerSpace P ⟶ P.groupoid.U.left :=
  P.groupoid.toPreRelation.stabilizer.hom.left

/-- The top arrow `𝒮_G ⟶ 𝒮_U` of the presentation-inertia square. -/
def stabilizerToObject : (stabilizerSpace P).toGroupoids ⟶ P.groupoid.U.left.toGroupoids :=
  toGroupoids.map (stabilizerStructure P)

/-- The top arrow is `𝒮` of the structure morphism of the stabilizer. -/
@[simp]
theorem stabilizerToObject_eq :
    stabilizerToObject P = toGroupoids.map (stabilizerStructure P) :=
  rfl

/-- The right vertical arrow `𝒮_U ⟶ X`, given by the atlas of `[U/R]` followed by the
presentation equivalence. -/
def presentationAtlas : P.groupoid.U.left.toGroupoids ⟶ X :=
  (SmallQuotient.atlas P.groupoid) ≫ P.hom

/-- The right vertical arrow factors as the atlas of the presenting groupoid followed by
the presentation equivalence. -/
@[simp]
theorem presentationAtlas_eq :
    presentationAtlas P = (SmallQuotient.atlas P.groupoid) ≫ P.hom :=
  rfl

/-- The image of a `T`-point of the stabilizer in `𝒮_U`. -/
private def stabilizerObjectPoint (x : (stabilizerSpace P).toGroupoids.total) :
    P.groupoid.U.left.toGroupoids.total :=
  (toFunctor (stabilizerToObject P)).obj x

/-- The atlas image of a stabilizer point in `[U /ₚ R]`. -/
private def stabilizerPreInertiaObj (x : (stabilizerSpace P).toGroupoids.total) :
    (SmallQuotient.preQuotient P.groupoid).total :=
  (SmallQuotient.atlasToPreQuotientFunctor P.groupoid).obj (stabilizerObjectPoint P x)

/-- The `T`-valued arrow of `R` carried by a point of the stabilizer. -/
private def stabilizerArrowPoint (x : (stabilizerSpace P).toGroupoids.total) :
    P.groupoid.R.left.functorOfPoints.obj (op x.unop.fst.unop) :=
  P.groupoid.toPreRelation.stabilizerToArrows.left.app (op x.unop.fst.unop) x.unop.snd

/-- A stabilizer arrow starts at the corresponding object of the groupoid prestack. -/
private theorem stabilizerPreInertiaAutHom_source
    (x : (stabilizerSpace P).toGroupoids.total) :
    P.groupoid.s.left.app (op x.unop.fst.unop) (stabilizerArrowPoint P x) =
      (stabilizerPreInertiaObj P x).fiber := sorry

/-- A stabilizer arrow ends at the identity restriction of its prestack object. -/
private theorem stabilizerPreInertiaAutHom_target
    (x : (stabilizerSpace P).toGroupoids.total) :
    P.groupoid.t.left.app (op x.unop.fst.unop) (stabilizerArrowPoint P x) =
      (P.groupoid.groupoidPresheaf.map (𝟙 (op (stabilizerPreInertiaObj P x).base))).obj
        (stabilizerPreInertiaObj P x).fiber := sorry

/-- The automorphism of the atlas image of a stabilizer point with underlying arrow the
stabilizer element. -/
private def stabilizerPreInertiaAutHom (x : (stabilizerSpace P).toGroupoids.total) :
    stabilizerPreInertiaObj P x ⟶ stabilizerPreInertiaObj P x where
  base := 𝟙 (stabilizerPreInertiaObj P x).base
  fiber :=
    FunctorPointHom.ofArrow (stabilizerArrowPoint P x)
      (stabilizerPreInertiaAutHom_source P x) (stabilizerPreInertiaAutHom_target P x)

/-- The inverse stabilizer arrow starts at the corresponding prestack object. -/
private theorem stabilizerPreInertiaAutInv_source
    (x : (stabilizerSpace P).toGroupoids.total) :
    P.groupoid.s.left.app (op x.unop.fst.unop)
        (P.groupoid.i.left.app (op x.unop.fst.unop) (stabilizerArrowPoint P x)) =
      (stabilizerPreInertiaObj P x).fiber := sorry

/-- The inverse stabilizer arrow ends at the identity restriction of its prestack object. -/
private theorem stabilizerPreInertiaAutInv_target
    (x : (stabilizerSpace P).toGroupoids.total) :
    P.groupoid.t.left.app (op x.unop.fst.unop)
        (P.groupoid.i.left.app (op x.unop.fst.unop) (stabilizerArrowPoint P x)) =
      (P.groupoid.groupoidPresheaf.map (𝟙 (op (stabilizerPreInertiaObj P x).base))).obj
        (stabilizerPreInertiaObj P x).fiber := sorry

/-- The inverse automorphism of the atlas image, using groupoid inversion. -/
private def stabilizerPreInertiaAutInv (x : (stabilizerSpace P).toGroupoids.total) :
    stabilizerPreInertiaObj P x ⟶ stabilizerPreInertiaObj P x where
  base := 𝟙 (stabilizerPreInertiaObj P x).base
  fiber :=
    FunctorPointHom.ofArrow
      (P.groupoid.i.left.app (op x.unop.fst.unop) (stabilizerArrowPoint P x))
      (stabilizerPreInertiaAutInv_source P x) (stabilizerPreInertiaAutInv_target P x)

/-- The stabilizer arrow followed by its inverse is the identity of its prestack object. -/
private theorem stabilizerPreInertiaAut_hom_inv_id
    (x : (stabilizerSpace P).toGroupoids.total) :
    stabilizerPreInertiaAutHom P x ≫ stabilizerPreInertiaAutInv P x =
      𝟙 (stabilizerPreInertiaObj P x) := sorry

/-- The inverse stabilizer arrow followed by the arrow is the identity of its prestack object. -/
private theorem stabilizerPreInertiaAut_inv_hom_id
    (x : (stabilizerSpace P).toGroupoids.total) :
    stabilizerPreInertiaAutInv P x ≫ stabilizerPreInertiaAutHom P x =
      𝟙 (stabilizerPreInertiaObj P x) := sorry

/-- The stabilizer automorphism of the atlas image of a stabilizer point. -/
private def stabilizerPreInertiaAut (x : (stabilizerSpace P).toGroupoids.total) :
    Aut (stabilizerPreInertiaObj P x) where
  hom := stabilizerPreInertiaAutHom P x
  inv := stabilizerPreInertiaAutInv P x
  hom_inv_id := stabilizerPreInertiaAut_hom_inv_id P x
  inv_hom_id := stabilizerPreInertiaAut_inv_hom_id P x

/-- The stabilizer automorphism lies over the identity of the test scheme. -/
private theorem stabilizerToPreInertiaObj_condition
    (x : (stabilizerSpace P).toGroupoids.total) :
    (SmallQuotient.preQuotient P.groupoid).p.mapAut
      (stabilizerPreInertiaObj P x) (stabilizerPreInertiaAut P x) = 1 := sorry

/-- The object of `I_{[U /ₚ R]}` sending a stabilizer point to its atlas image equipped with
the automorphism given by `stabilizerToArrows`. -/
private def stabilizerToPreInertiaObj (x : (stabilizerSpace P).toGroupoids.total) :
    RelativeInertia (SmallQuotient.preQuotient P.groupoid).p :=
  RelativeInertia.mk (Inertia.mk (stabilizerPreInertiaObj P x) (stabilizerPreInertiaAut P x))
    (stabilizerToPreInertiaObj_condition P x)

/-- A morphism of stabilizer points intertwines their prestack automorphisms. -/
private theorem stabilizerToPreInertiaMap_naturality
    {x y : (stabilizerSpace P).toGroupoids.total} (φ : x ⟶ y) :
    (stabilizerToPreInertiaObj P x).aut.hom ≫
        (SmallQuotient.atlasToPreQuotientFunctor P.groupoid).map
          ((toFunctor (stabilizerToObject P)).map φ) =
      (SmallQuotient.atlasToPreQuotientFunctor P.groupoid).map
          ((toFunctor (stabilizerToObject P)).map φ) ≫
        (stabilizerToPreInertiaObj P y).aut.hom := sorry

/-- The morphism of `I_{[U /ₚ R]}` induced by a morphism of `𝒮_G`. -/
private def stabilizerToPreInertiaMap {x y : (stabilizerSpace P).toGroupoids.total} (φ : x ⟶ y) :
    stabilizerToPreInertiaObj P x ⟶ stabilizerToPreInertiaObj P y :=
  RelativeInertia.homMk (SmallQuotient.preQuotient P.groupoid).p
    ((SmallQuotient.atlasToPreQuotientFunctor P.groupoid).map ((toFunctor (stabilizerToObject P)).map φ))
    (stabilizerToPreInertiaMap_naturality P φ)

/-- The stabilizer-to-inertia arrow assignment preserves identity morphisms. -/
private theorem stabilizerToPreInertiaFunctor_map_id
    (x : (stabilizerSpace P).toGroupoids.total) :
    stabilizerToPreInertiaMap P (𝟙 x) = 𝟙 (stabilizerToPreInertiaObj P x) := sorry

/-- The stabilizer-to-inertia arrow assignment preserves composition. -/
private theorem stabilizerToPreInertiaFunctor_map_comp
    {x y z : (stabilizerSpace P).toGroupoids.total} (φ : x ⟶ y) (ψ : y ⟶ z) :
    stabilizerToPreInertiaMap P (φ ≫ ψ) =
      stabilizerToPreInertiaMap P φ ≫ stabilizerToPreInertiaMap P ψ := sorry

/-- The total functor `𝒮_G ⟶ I_{[U /ₚ R]}`. -/
private def stabilizerToPreInertiaFunctor :
    (stabilizerSpace P).toGroupoids.total ⥤ RelativeInertia (SmallQuotient.preQuotient P.groupoid).p where
  obj := stabilizerToPreInertiaObj P
  map := stabilizerToPreInertiaMap P
  map_id := stabilizerToPreInertiaFunctor_map_id P
  map_comp := stabilizerToPreInertiaFunctor_map_comp P

/-- `stabilizerToPreInertiaFunctor` commutes with projection to `Over S`. -/
private theorem stabilizerToPreInertia_w :
    stabilizerToPreInertiaFunctor P ⋙
        (inertia (SmallQuotient.preQuotient P.groupoid)).p =
      (stabilizerSpace P).toGroupoids.p :=
  sorry

/-- The `1`-morphism `𝒮_G ⟶ I_{[U /ₚ R]}`. -/
def stabilizerToPreInertia :
    (stabilizerSpace P).toGroupoids ⟶
      inertia (SmallQuotient.preQuotient P.groupoid) :=
  ofBasedFunctor
    { toFunctor := stabilizerToPreInertiaFunctor P
      w := stabilizerToPreInertia_w P }

/-- The `1`-morphism `𝒮_G ⟶ I_{[U/R]}` obtained by applying inertia of stackification. -/
def stabilizerToQuotientInertia :
    (stabilizerSpace P).toGroupoids ⟶
      inertia (SmallQuotient.quotientStack P.groupoid) :=
  stabilizerToPreInertia P ≫ map.{u + 1, u, u, u + 1} (SmallQuotient.stackificationHom P.groupoid)

/-- The left vertical arrow `𝒮_G ⟶ I_X` of the presentation-inertia square. -/
def stabilizerToInertia :
    (stabilizerSpace P).toGroupoids ⟶ inertia X :=
  stabilizerToQuotientInertia P ≫ map.{u + 1, u, u, u + 1} P.hom

/-- After forgetting automorphisms, `stabilizerToInertia` is the composite of the
stabilizer structure map with the presentation atlas. -/
theorem stabilizerToInertia_comp_forget :
    stabilizerToInertia P ≫ forget.{u + 1, u, u, u + 1} X =
      stabilizerToObject P ≫ presentationAtlas P :=
  sorry

/-- The invertible `2`-cell of the presentation-inertia square. -/
def presentationInertiaIso :
    stabilizerToInertia P ≫ forget.{u + 1, u, u, u + 1} X ≅
      stabilizerToObject P ≫ presentationAtlas P :=
  eqToIso (stabilizerToInertia_comp_forget P)

/-- The `2`-commutative square with apex `𝒮_G`, first leg `𝒮_G ⟶ I_X`, second leg
`𝒮_G ⟶ 𝒮_U`, and cospan `I_X ⟶ X ← 𝒮_U`. -/
def presentationInertiaCone :
    PseudoPullbackCone (forget.{u + 1, u, u, u + 1} X) (presentationAtlas P) where
  pt := (stabilizerSpace P).toGroupoids
  fst := stabilizerToInertia P
  snd := stabilizerToObject P
  iso := presentationInertiaIso P

/-- The apex of `presentationInertiaCone P` is `𝒮_G`. -/
@[simp]
theorem presentationInertiaCone_pt :
    (presentationInertiaCone P).pt = (stabilizerSpace P).toGroupoids :=
  rfl

/-- The first projection of `presentationInertiaCone P` is `𝒮_G ⟶ I_X`. -/
@[simp]
theorem presentationInertiaCone_fst :
    (presentationInertiaCone P).fst = stabilizerToInertia P :=
  rfl

/-- The second projection of `presentationInertiaCone P` is `𝒮_G ⟶ 𝒮_U`. -/
@[simp]
theorem presentationInertiaCone_snd :
    (presentationInertiaCone P).snd = stabilizerToObject P :=
  rfl

/-- The `2`-cell of `presentationInertiaCone P` is `presentationInertiaIso P`. -/
@[simp]
theorem presentationInertiaCone_iso :
    (presentationInertiaCone P).iso = presentationInertiaIso P :=
  rfl

/-- For an algebraic stack with a presentation, the canonical square from its stabilizer
algebraic space to the presentation object space and from its inertia stack to the stack
is a bicategorical fibre product. -/
theorem presentationInertiaCone_isBilimit :
    (presentationInertiaCone P).IsBilimit :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Inertia
