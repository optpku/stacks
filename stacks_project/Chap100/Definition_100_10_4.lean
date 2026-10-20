/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap100.Definition_100_10_4_Structure
public import stacks_project.Chap100.Definition_100_10_4_Reduced
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open TopologicalSpace
open CategoryTheory
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Definition 100.10.4 (1): an algebraic stack structure on a closed subset `Z` of
`Points X` is a closed substack `Z'` of `X` with `Z'.pointsSet` equal to `Z`. -/
@[stacks 050C] #check (AlgebraicGeometry.AlgebraicStack.ClosedSubstackStructure :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X],
    Closeds (Points X) → Type (u + 1))
#check (AlgebraicGeometry.AlgebraicStack.ClosedSubstackStructure.ofSubstack :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Z : Closeds (Points X)} (W : ClosedSubstack X),
    W.pointsSet = Z.carrier → ClosedSubstackStructure Z)
#check (AlgebraicGeometry.AlgebraicStack.ClosedSubstackStructure.Y :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Z : Closeds (Points X)}, ClosedSubstackStructure Z → GroupoidsOver S)
#check (AlgebraicGeometry.AlgebraicStack.ClosedSubstackStructure.ι :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Z : Closeds (Points X)} (T : ClosedSubstackStructure Z), T.Y ⟶ X)
#check (AlgebraicGeometry.AlgebraicStack.ClosedSubstackStructure.spec :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Z : Closeds (Points X)} (T : ClosedSubstackStructure Z),
    ClosedImmersion T.ι ∧ Set.range (Points.map T.ι) = Z.carrier)

/- Definition 100.10.4 (2): the reduced induced algebraic stack structure on `Z` is
the one constructed in Lemma 100.10.1. -/
@[stacks 050C] #check (AlgebraicGeometry.AlgebraicStack.ClosedSubstackStructure.reduced :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (Z : Closeds (Points X)), ClosedSubstackStructure Z)
#check (AlgebraicGeometry.AlgebraicStack.ClosedSubstackStructure.reduced_spec :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (Z : Closeds (Points X)),
    Set.range (Points.map (ClosedSubstackStructure.reduced Z).ι) = Z.carrier ∧
      IsReduced (ClosedSubstackStructure.reduced Z).Y)

/- Definition 100.10.4 (3): the reduction `X_red` of `X` is the reduced induced
algebraic stack structure on `Points X`. -/
@[stacks 050C] #check (AlgebraicGeometry.AlgebraicStack.reduction :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X], GroupoidsOver S)
#check (AlgebraicGeometry.AlgebraicStack.reductionι :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X], reduction X ⟶ X)
#check (AlgebraicGeometry.AlgebraicStack.reduction_spec :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    IsReduced (reduction X) ∧ ClosedImmersion (reductionι X) ∧
      Function.Surjective (Points.map (reductionι X)))

end AlgebraicGeometry.AlgebraicStack
