/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.CompletionAlong
public import stacks_project.Chap87.Lemma_87_34_3_Reduction

/-!
# Completion using the legacy reduction interface

The class-based completion interface specializes completion with explicit
reduction data to the chosen legacy reduction.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.AlgebraicSpace (Points)

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- A section maps into a subset if the image of its reduced source lies in that subset. -/
def mapsInto {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [R : Reduction X]
    (T : Set (Points (reduction X))) {U : Over S} (x : X.obj (op U)) : Prop :=
  Recompletion.mapsInto R.toReductionData T x

/-- Completion along a closed subset of the chosen reduction. -/
def completionAlong {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [R : Reduction X]
    (T : Closeds (Points (reduction X))) : (Over S)ᵒᵖ ⥤ Type u :=
  Recompletion.functor R.toReductionData T

/-- Completion along a closed subset of the chosen reduction is a formal algebraic space. -/
instance instIsFormalAlgebraicSpace_completionAlong {S : Scheme.{u}}
    (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X] [R : Reduction X]
    (T : Closeds (Points (reduction X))) :
    IsFormalAlgebraicSpace (completionAlong X T) :=
  Recompletion.isFormalAlgebraicSpace R.toReductionData T

namespace completionAlong

/-- The canonical inclusion of completion into its ambient formal algebraic space. -/
def ι {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [R : Reduction X]
    (T : Closeds (Points (reduction X))) : completionAlong X T ⟶ X :=
  Recompletion.ι R.toReductionData T

end completionAlong

end AlgebraicGeometry.FormalAlgebraicSpace
