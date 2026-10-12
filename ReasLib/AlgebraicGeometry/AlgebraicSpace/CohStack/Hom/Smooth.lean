/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom

/-!
# Smooth morphisms of groupoid fibrations over schemes

A 1-morphism of categories fibred in groupoids over `Over S` is smooth when it admits a
presentation by scheme slices whose comparison morphism of schemes is smooth.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack.Hom

/-- The universe-lifted slice projection of a scheme over `S`. -/
def schemeSliceProjection {S : Scheme.{u}} (U : Over S) :
    ULiftHom.{u + 1} (Over U) ⥤ Over S :=
  (ULiftHom.down : ULiftHom.{u + 1} (Over U) ⥤ Over U) ⋙ Over.forget U

/-- The universe-lifted slice projection is fibred in groupoids. -/
instance instIsFiberedInGroupoids_schemeSlice {S : Scheme.{u}} (U : Over S) :
    Functor.IsFibered.InGroupoids (schemeSliceProjection U) :=
  sorry

/-- The canonical scheme slice of an object of `Over S`, as a category fibred in groupoids. -/
def schemeSlice {S : Scheme.{u}} (U : Over S) :
    FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S) :=
  Groupoids.ofFunctor.{u + 1, u, u + 1, u + 1} (schemeSliceProjection U)

/-- The projection of `schemeSlice U` is `schemeSliceProjection U`. -/
theorem schemeSlice_p {S : Scheme.{u}} (U : Over S) :
    (schemeSlice U).p = schemeSliceProjection U :=
  Groupoids.ofFunctor.p (schemeSliceProjection U)

/-- The total functor of scheme slices induced by a morphism in `Over S`. -/
def schemeSliceFunctor {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V) :
    ULiftHom.{u + 1} (Over U) ⥤ ULiftHom.{u + 1} (Over V) :=
  (ULiftHom.down : ULiftHom.{u + 1} (Over U) ⥤ Over U) ⋙ Over.map h ⋙ ULiftHom.up

/-- A 1-morphism `f : X ⟶ Y` of categories fibred in groupoids over `Over S` is smooth if it
admits scheme slices `U`, `V` and structure maps `a`, `b`, `h` with `AlgebraicGeometry.Smooth`
on `h.left`. -/
class Smooth {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) : Prop where
  /-- There are scheme slices and structure maps presenting `f` with a smooth comparison. -/
  exists_smooth_scheme_presentation :
    ∃ (U V : Over S) (a : schemeSlice U ⟶ X) (b : schemeSlice V ⟶ Y) (h : U ⟶ V),
      AlgebraicGeometry.Smooth h.left ∧
        Groupoids.toFunctor a ⋙ Groupoids.toFunctor f =
          schemeSliceFunctor h ⋙ Groupoids.toFunctor b

/-- A 1-morphism is smooth if and only if it admits a scheme-slice presentation whose comparison
morphism of schemes is smooth. -/
theorem smooth_iff {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) :
    Smooth f ↔
      ∃ (U V : Over S) (a : schemeSlice U ⟶ X) (b : schemeSlice V ⟶ Y) (h : U ⟶ V),
        AlgebraicGeometry.Smooth h.left ∧
          Groupoids.toFunctor a ⋙ Groupoids.toFunctor f =
            schemeSliceFunctor h ⋙ Groupoids.toFunctor b :=
  sorry

namespace Smooth

/-- The identity 1-morphism of a category fibred in groupoids is smooth. -/
instance id {S : Scheme.{u}}
    {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)} :
    Smooth (𝟙 X) :=
  sorry

/-- A smooth 1-morphism admits a scheme-slice presentation with smooth comparison morphism. -/
theorem spec {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) [Smooth f] :
    ∃ (U V : Over S) (a : schemeSlice U ⟶ X) (b : schemeSlice V ⟶ Y) (h : U ⟶ V),
      AlgebraicGeometry.Smooth h.left ∧
        Groupoids.toFunctor a ⋙ Groupoids.toFunctor f =
          schemeSliceFunctor h ⋙ Groupoids.toFunctor b :=
  sorry

end Smooth

end AlgebraicGeometry.AlgebraicSpace.CohStack.Hom
