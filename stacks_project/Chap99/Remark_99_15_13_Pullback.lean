/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Resize
public import stacks_project.Chap99.Lemma_99_15_2
public import stacks_project.Chap109.Lemma_109_4_1_PolarizedCurves

/-!
# PolarizedCurves as a 2-fibre product over Spaces'_{fp, flat, proper}

The forgetful functor PolarizedCurves ⥤ Curves is the left vertical arrow of the
2-fibre product square of Curves ⟶ Spaces'_{fp, flat, proper} along
Polarized ⟶ Spaces'_{fp, flat, proper}. PolarizedCurves remains the full
subcategory of Polarized on relative dimension at most 1; this module packages
the square and the Hom-universe `u + 1` 1-morphism to Curves.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces hiding p
open CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoricalPullback
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.PolarizedCurves

/-- Forgetting the line bundle of a polarized curve family yields an object of
the stack of curves. -/
theorem toFpFlatProper_mem (P : Obj) :
    Curves.relativeDimensionLE (⊤_ Scheme.{u}) 1
      (Polarized.toFpFlatProper.obj P.obj) :=
  sorry

/-- The forgetful functor PolarizedCurves ⥤ Curves, sending a polarized curve
family to the underlying family of curves over the terminal scheme. -/
def toCurves : Obj ⥤ Curves.Obj (⊤_ Scheme.{u}) :=
  (Curves.relativeDimensionLE (⊤_ Scheme.{u}) 1).lift
    (inclusion ⋙ Polarized.toFpFlatProper) toFpFlatProper_mem

/-- The object part of `toCurves` is the forgotten polarized family, viewed in
the stack of curves. -/
theorem toCurves_obj (P : Obj) :
    (toCurves.obj P).obj = Polarized.toFpFlatProper.obj P.obj :=
  sorry

/-- Composing `toCurves` with the inclusion of Curves into
`Spaces'_{fp, flat, proper}` recovers the Polarized forgetful functor. -/
theorem toCurves_comp_inclusion :
    toCurves ⋙ Curves.inclusion (⊤_ Scheme.{u}) =
      inclusion ⋙ Polarized.toFpFlatProper :=
  sorry

/-- The commutative square with apex PolarizedCurves, projecting to Curves and
to Polarized over `Spaces'_{fp, flat, proper}`. -/
def square :
    CatCommSqOver (Curves.inclusion (⊤_ Scheme.{u})) Polarized.toFpFlatProper
      Obj where
  fst := toCurves
  snd := inclusion
  iso :=
    (Curves.relativeDimensionLE (⊤_ Scheme.{u}) 1).liftCompιIso
      (inclusion ⋙ Polarized.toFpFlatProper) toFpFlatProper_mem

/-- The first projection of `square` is `toCurves`. -/
theorem square_fst : square.fst = toCurves :=
  sorry

/-- The second projection of `square` is the inclusion PolarizedCurves ⥤
Polarized. -/
theorem square_snd : square.snd = inclusion :=
  sorry

/-- The comparison from PolarizedCurves to the explicit categorical pullback of
Curves ⟶ Spaces'_{fp, flat, proper} along Polarized ⟶ Spaces'_{fp, flat, proper}. -/
abbrev comparison := square.comparison

/-- The comparison functor is an equivalence when `square` is a 2-fibre product. -/
instance comparison_isEquivalence [CatCommSqOver.Resized.IsBilimit square] :
    comparison.IsEquivalence :=
  sorry

/-- The universe-lifted projection of PolarizedCurves to `Over (⊤_ Scheme)`. -/
def toGroupoidsProjection : ULiftHom.{u + 1} Obj ⥤ Over (⊤_ Scheme.{u}) :=
  (ULiftHom.down : ULiftHom.{u + 1} Obj ⥤ Obj) ⋙ p ⋙ Polarized.asOverTerminal

/-- The universe-lifted projection of PolarizedCurves is fibred in groupoids. -/
instance instIsFiberedInGroupoids_toGroupoids :
    Functor.IsFibered.InGroupoids toGroupoidsProjection :=
  sorry

/-- PolarizedCurves, bundled as a category fibred in groupoids over
`Over (⊤_ Scheme)` at Hom-universe `u + 1`. -/
def toGroupoids :
    FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1}
      (Over (⊤_ Scheme.{u})) :=
  Groupoids.ofFunctor.{u + 1, u, u + 1, u + 1} toGroupoidsProjection

/-- The projection of `toGroupoids` is `toGroupoidsProjection`. -/
theorem toGroupoids_p : toGroupoids.p = toGroupoidsProjection :=
  sorry

/-- The 1-morphism PolarizedCurves ⟶ Curves, packaged as a morphism of
categories fibred in groupoids over `Over (⊤_ Scheme)`. The underlying functor
is the universe lift of `toCurves`. -/
def toCurvesHom : toGroupoids ⟶ Curves.toGroupoids (⊤_ Scheme.{u}) :=
  Groupoids.ofBasedFunctor
    { toFunctor := (ULiftHom.down : ULiftHom.{u + 1} Obj ⥤ Obj) ⋙ toCurves
      w := sorry }

/-- The underlying functor of `toCurvesHom` is the universe lift of `toCurves`. -/
theorem toCurvesHom_toFunctor :
    Groupoids.toFunctor toCurvesHom =
      (ULiftHom.down : ULiftHom.{u + 1} Obj ⥤ Obj) ⋙ toCurves :=
  sorry

/-- `toCurvesHom` lies strictly over `Over (⊤_ Scheme)`. -/
theorem toCurvesHom_comm :
    Groupoids.toFunctor toCurvesHom ⋙ (Curves.toGroupoids (⊤_ Scheme.{u})).p =
      toGroupoids.p :=
  sorry

end AlgebraicGeometry.PolarizedCurves
