module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsoluteTransformations.Maps.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.Functoriality.Construction
public import ReasLib.CategoryTheory.Inertia.Relative
public import stacks_project.Chap78.Lemma_78_26_1_Presentation
public import stacks_project.Chap94.Definition_94_16_5_Presentation

/-!
# Stabilizer square of a presentation of an algebraic stack

A presentation `P : [U/R] ⟶ X` determines a 2-commutative square in
`GroupoidsOver S` with vertices `𝒮_G`, `𝒮_U`, `I_X`, and `X`, where `G/U` is
the stabilizer group algebraic space of the presenting groupoid.
-/

@[expose] public section

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
  sorry

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
  sorry

/-- The right vertical arrow `𝒮_U ⟶ X`, given by the atlas of `[U/R]` followed by the
presentation equivalence. -/
def presentationAtlas : P.groupoid.U.left.toGroupoids ⟶ X :=
  P.groupoid.atlas ≫ P.hom

/-- The right vertical arrow factors as the atlas of the presenting groupoid followed by
the presentation equivalence. -/
@[simp]
theorem presentationAtlas_eq :
    presentationAtlas P = P.groupoid.atlas ≫ P.hom :=
  sorry

/-- The image of a `T`-point of the stabilizer in `𝒮_U`. -/
def stabilizerObjectPoint (x : (stabilizerSpace P).toGroupoids.total) :
    P.groupoid.U.left.toGroupoids.total :=
  (toFunctor (stabilizerToObject P)).obj x

/-- The atlas image of a stabilizer point in `[U /ₚ R]`. -/
def stabilizerPreInertiaObj (x : (stabilizerSpace P).toGroupoids.total) :
    P.groupoid.preQuotient.total :=
  P.groupoid.atlasToPreQuotientFunctor.obj (stabilizerObjectPoint P x)

/-- The `T`-valued arrow of `R` carried by a point of the stabilizer. -/
def stabilizerArrowPoint (x : (stabilizerSpace P).toGroupoids.total) :
    P.groupoid.R.left.functorOfPoints.obj (op x.unop.fst.unop) :=
  P.groupoid.toPreRelation.stabilizerToArrows.left.app (op x.unop.fst.unop) x.unop.snd

/-- The automorphism of the atlas image of a stabilizer point with underlying arrow the
stabilizer element. -/
def stabilizerPreInertiaAutHom (x : (stabilizerSpace P).toGroupoids.total) :
    stabilizerPreInertiaObj P x ⟶ stabilizerPreInertiaObj P x where
  base := 𝟙 (stabilizerPreInertiaObj P x).base
  fiber :=
    FunctorPointHom.ofArrow (stabilizerArrowPoint P x) sorry sorry

/-- The inverse automorphism of the atlas image, using groupoid inversion. -/
def stabilizerPreInertiaAutInv (x : (stabilizerSpace P).toGroupoids.total) :
    stabilizerPreInertiaObj P x ⟶ stabilizerPreInertiaObj P x where
  base := 𝟙 (stabilizerPreInertiaObj P x).base
  fiber :=
    FunctorPointHom.ofArrow
      (P.groupoid.i.left.app (op x.unop.fst.unop) (stabilizerArrowPoint P x)) sorry sorry

/-- The chosen automorphism of the atlas image of a stabilizer point. -/
def stabilizerPreInertiaAut (x : (stabilizerSpace P).toGroupoids.total) :
    Aut (stabilizerPreInertiaObj P x) where
  hom := stabilizerPreInertiaAutHom P x
  inv := stabilizerPreInertiaAutInv P x
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The object of `I_{[U /ₚ R]}` sending a stabilizer point to its atlas image equipped with
the automorphism given by `stabilizerToArrows`. -/
def stabilizerToPreInertiaObj (x : (stabilizerSpace P).toGroupoids.total) :
    RelativeInertia P.groupoid.preQuotient.p where
  obj := stabilizerPreInertiaObj P x
  aut := stabilizerPreInertiaAut P x
  mapAut_eq_one := sorry

/-- The morphism of `I_{[U /ₚ R]}` induced by a morphism of `𝒮_G`. -/
def stabilizerToPreInertiaMap {x y : (stabilizerSpace P).toGroupoids.total} (φ : x ⟶ y) :
    stabilizerToPreInertiaObj P x ⟶ stabilizerToPreInertiaObj P y :=
  RelativeInertia.homMk P.groupoid.preQuotient.p
    (P.groupoid.atlasToPreQuotientFunctor.map ((toFunctor (stabilizerToObject P)).map φ))
    sorry

/-- The total functor `𝒮_G ⟶ I_{[U /ₚ R]}`. -/
def stabilizerToPreInertiaFunctor :
    (stabilizerSpace P).toGroupoids.total ⥤ RelativeInertia P.groupoid.preQuotient.p where
  obj := stabilizerToPreInertiaObj P
  map := stabilizerToPreInertiaMap P
  map_id := sorry
  map_comp := sorry

/-- `stabilizerToPreInertiaFunctor` commutes with projection to `Over S`. -/
theorem stabilizerToPreInertia_w :
    stabilizerToPreInertiaFunctor P ⋙
        (inertia P.groupoid.preQuotient).p =
      (stabilizerSpace P).toGroupoids.p :=
  sorry

/-- The `1`-morphism `𝒮_G ⟶ I_{[U /ₚ R]}`. -/
def stabilizerToPreInertia :
    (stabilizerSpace P).toGroupoids ⟶
      inertia P.groupoid.preQuotient :=
  ofBasedFunctor
    { toFunctor := stabilizerToPreInertiaFunctor P
      w := stabilizerToPreInertia_w P }

/-- The `1`-morphism `𝒮_G ⟶ I_{[U/R]}` obtained by applying inertia of stackification. -/
def stabilizerToQuotientInertia :
    (stabilizerSpace P).toGroupoids ⟶
      inertia P.groupoid.quotientStack :=
  stabilizerToPreInertia P ≫ map.{u + 1, u, u, u + 1} P.groupoid.stackificationHom

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
  sorry

/-- The first projection of `presentationInertiaCone P` is `𝒮_G ⟶ I_X`. -/
@[simp]
theorem presentationInertiaCone_fst :
    (presentationInertiaCone P).fst = stabilizerToInertia P :=
  sorry

/-- The second projection of `presentationInertiaCone P` is `𝒮_G ⟶ 𝒮_U`. -/
@[simp]
theorem presentationInertiaCone_snd :
    (presentationInertiaCone P).snd = stabilizerToObject P :=
  sorry

/-- The `2`-cell of `presentationInertiaCone P` is `presentationInertiaIso P`. -/
@[simp]
theorem presentationInertiaCone_iso :
    (presentationInertiaCone P).iso = presentationInertiaIso P :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Inertia
