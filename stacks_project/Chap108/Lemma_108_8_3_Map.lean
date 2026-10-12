/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import stacks_project.Chap99.Lemma_99_11_2_IsoClasses
public import stacks_project.Chap108.Lemma_108_8_4_Stack
public import stacks_project.Chap110.Lemma_110_53_1

/-!
# Structure morphism of the Picard stack

The forgetful 1-morphism `Pic_{X/B} ⟶ B` in the Hom-universe of
`Classifying.toGroupoids`, sending a triple `(T, g, L)` to the functor-of-points
element of `g : T ⟶ B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open AlgebraicGeometry.GroupScheme
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Picard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The functor-of-points section of a morphism of algebraic spaces from a
scheme over `S`. -/
def functorOfPointsSection {T : Over S} (φ : ofOver T ⟶ B) :
    B.functorOfPoints.obj (op T) :=
  yonedaEquiv (φ : yoneda.obj T ⟶ B.functorOfPoints)

/-- `functorOfPointsSection φ` is the Yoneda evaluation of `φ`. -/
theorem functorOfPointsSection_eq {T : Over S} (φ : ofOver T ⟶ B) :
    functorOfPointsSection φ = yonedaEquiv (φ : yoneda.obj T ⟶ B.functorOfPoints) :=
  sorry

/-- The category-of-elements object classified by the structure map of a Picard
object. -/
def toBaseElement {f : X ⟶ B} (x : Obj f) : B.functorOfPoints.Elements :=
  ⟨op x.σ.left, functorOfPointsSection x.σ.hom⟩

/-- The first component of `toBaseElement x` is the opposite of the test scheme
of `x`. -/
theorem toBaseElement_fst {f : X ⟶ B} (x : Obj f) :
    (toBaseElement x).fst = op x.σ.left :=
  sorry

/-- The second component of `toBaseElement x` is the functor-of-points section of
the structure map of `x`. -/
theorem toBaseElement_snd {f : X ⟶ B} (x : Obj f) :
    (toBaseElement x).snd = functorOfPointsSection x.σ.hom :=
  sorry

/-- Compatibility of functor-of-points sections with a morphism of Picard
objects. -/
theorem toBaseHom_map_snd {f : X ⟶ B} {x y : Obj f} (α : x ⟶ y) :
    B.functorOfPoints.map α.base.left.op (functorOfPointsSection y.σ.hom) =
      functorOfPointsSection x.σ.hom :=
  sorry

/-- The category-of-elements morphism induced by a Picard morphism, pointing
from the target test scheme to the source so that its opposite lies over
`α.base.left`. -/
def toBaseHom {f : X ⟶ B} {x y : Obj f} (α : x ⟶ y) :
    toBaseElement y ⟶ toBaseElement x :=
  CategoryOfElements.homMk (toBaseElement y) (toBaseElement x) α.base.left.op
    (toBaseHom_map_snd α)

/-- The underlying morphism of `toBaseHom α` is the opposite of the test-scheme
map of `α`. -/
theorem toBaseHom_val {f : X ⟶ B} {x y : Obj f} (α : x ⟶ y) :
    (toBaseHom α).val = α.base.left.op :=
  sorry

/-- The total functor of the structure morphism `Pic_{X/B} ⟶ B`, sending a
Picard object to the universe-lifted functor-of-points element of its
structure map. -/
def toBaseFunctor (f : X ⟶ B) :
    Obj f ⥤ ULiftHom.{u + 1} B.functorOfPoints.Elementsᵒᵖ where
  obj x := ULiftHom.objUp (op (toBaseElement x))
  map α := ULiftHom.up.map (Quiver.Hom.op (toBaseHom α))
  map_id := sorry
  map_comp := sorry

/-- On objects, `toBaseFunctor` is `ULiftHom.objUp` of the opposite
category-of-elements object. -/
theorem toBaseFunctor_obj (f : X ⟶ B) (x : Obj f) :
    (toBaseFunctor f).obj x = ULiftHom.objUp (op (toBaseElement x)) :=
  sorry

/-- `toBaseFunctor` lies strictly over `(Sch/S)`. -/
theorem toBaseFunctor_p (f : X ⟶ B) :
    toBaseFunctor f ⋙ Classifying.toGroupoidsProjection B = p f :=
  sorry

/-- The structure 1-morphism `Pic_{X/B} ⟶ B` in the Hom-universe of
`Classifying.toGroupoids`, forgetting the invertible module and recording the
test scheme over `B`. -/
def toBase (f : X ⟶ B) :
    ((picardStack f).toGroupoids :
        FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)) ⟶
      Classifying.toGroupoids B :=
  ofBasedFunctor { toFunctor := toBaseFunctor f, w := sorry }

/-- The total functor of `toBase f` is `toBaseFunctor f`. -/
theorem toBase_toFunctor (f : X ⟶ B) :
    toFunctor (toBase f) = toBaseFunctor f :=
  sorry

/-- `toBase f` lies strictly over `(Sch/S)`. -/
theorem toBase_p (f : X ⟶ B) :
    toFunctor (toBase f) ⋙ (Classifying.toGroupoids B).p = (picardStack f).p :=
  sorry

/-- On a Picard object `x`, `toBase f` is the universe-lifted functor-of-points
element of the structure map of `x`. -/
theorem toBase_obj (f : X ⟶ B) (x : Obj f) :
    (toFunctor (toBase f)).obj x = ULiftHom.objUp (op (toBaseElement x)) :=
  sorry

/-- `toBase` forgets the invertible module and records the test scheme of
`toSchemesOver`. -/
theorem toBase_spec (f : X ⟶ B) (x : Obj f) :
    (Classifying.toGroupoidsProjection B).obj ((toFunctor (toBase f)).obj x) =
      ((toSchemesOver f).obj x).left :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Picard
