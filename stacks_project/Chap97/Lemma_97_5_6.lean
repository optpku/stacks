module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.CategoryTheory.Fibered.Groupoids.Base
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids
public import stacks_project.Chap73.Lemma_73_7_3_Precoverage
public import stacks_project.Chap97.«97_5_0_1_OnObjects»
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty

/-!
# Checking a morphism property using limit preservation on objects

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
representable by algebraic spaces has a property `P` as in Definition 94.10.1
as soon as the target is limit preserving on objects and affine locally finite
presentation tests have `P`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Functor.Fiber
open FiberedCategoryOver.Groupoids
open FiberedCategoryOver.Groupoids.YonedaSlice
open AlgebraicSpace
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- Lemma 97.5.6: Let `S` be a scheme. Let `f : X ⟶ Y` be a 1-morphism of
categories fibred in groupoids over `(Sch/S)_fppf`. Let `P` be a property of
morphisms of algebraic spaces as in Algebraic Stacks, Definition 94.10.1. If
`f` is representable by algebraic spaces, `Y ⟶ (Sch/S)_fppf` is limit
preserving on objects, and for an affine scheme `V` locally of finite
presentation over `S` and `y : Y.p.Fiber V` the resulting morphism of
algebraic spaces `fy : Fy ⟶ ofOver V` of Equation 94.9.1.1 has property `P`,
then `f` has property `P`. -/
@[stacks 07WI]
theorem has.of_limitPreservingOnObjects {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    {f : X ⟶ Y} (hf : relativelyRepresentableByAlgebraicSpaces f)
    [LimitPreservingOnObjects (baseProjection.{u + 1, u, u + 1} Y)]
    (h : ∀ (V : Over S) [IsAffine V.left] [LocallyOfFinitePresentation V.hom]
      (y : Y.p.Fiber V) (Fy : AlgebraicSpace S) (fy : Fy ⟶ ofOver V),
      RepresentsBaseChange f (YonedaSlice.representative y) Fy fy → P fy) :
    has P f :=
  sorry

/-- The same criterion, stated with slice tests `y : GroupoidsOver.slice V ⟶ Y`
in the form used by `has`. -/
theorem has.of_limitPreservingOnObjects_slice {S : Scheme.{u}}
    {X Y : GroupoidsOver S} (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    {f : X ⟶ Y} (hf : relativelyRepresentableByAlgebraicSpaces f)
    [LimitPreservingOnObjects (baseProjection.{u + 1, u, u + 1} Y)]
    (h : ∀ (V : Over S) [IsAffine V.left] [LocallyOfFinitePresentation V.hom]
      (y : GroupoidsOver.slice V ⟶ Y) (Fy : AlgebraicSpace S)
      (fy : Fy ⟶ ofOver V), RepresentsBaseChange f y Fy fy → P fy) :
    has P f :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
