/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.CompletionAlong
public import stacks_project.Chap87.Lemma_87_34_3_Reduction

/-!
# Completion of a formal algebraic space along a closed subset

Completion and its canonical inclusion are supplied by `Recompletion`.
The class-based reduction interface supplies the explicit reduction data.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.AlgebraicSpace (Points)

universe u

open AlgebraicGeometry.FormalAlgebraicSpace

attribute [instance] Recompletion.isFormalAlgebraicSpace

#check @Reduction.toReductionData

/- A section maps into a subset if the image of its reduced source lies in that subset. -/
#check (Recompletion.mapsInto :
    ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
      (R : ReductionData X) (T : Set (Points R.space)) {U : Over S}
      (x : X.obj (op U)), Prop)

/- Completion along a closed subset of the reduction. -/
#check (Recompletion.functor :
    ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
      (R : ReductionData X) (T : Closeds (Points R.space)),
      (Over S)ᵒᵖ ⥤ Type u)

/- Completion along a closed subset of the reduction is a formal algebraic space. -/
#check (Recompletion.isFormalAlgebraicSpace :
    ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
      (R : ReductionData X) (T : Closeds (Points R.space)),
      IsFormalAlgebraicSpace (Recompletion.functor R T))

/- The canonical inclusion of completion into its ambient formal algebraic space. -/
#check (Recompletion.ι :
    ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
      (R : ReductionData X) (T : Closeds (Points R.space)),
      Recompletion.functor R T ⟶ X)
