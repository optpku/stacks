/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ResidualGerbe
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Definition 100.11.8 (1): the residual gerbe of an algebraic stack `X` at a
point `x ∈ |X|` exists if the equivalent conditions of Lemma 100.11.7 hold. -/
@[stacks 06MU] #check (AlgebraicGeometry.AlgebraicStack.HasResidualGerbe :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X], Points X → Prop)
#check (AlgebraicGeometry.AlgebraicStack.HasResidualGerbe.iff_existsMonoSingletonAt :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] {x : Points X},
    HasResidualGerbe X x ↔ existsMonoSingletonAt X x)
#check (AlgebraicGeometry.AlgebraicStack.HasResidualGerbe.iff_existsReducedMonoSingletonAt :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] {x : Points X},
    HasResidualGerbe X x ↔ existsReducedMonoSingletonAt X x)
#check (AlgebraicGeometry.AlgebraicStack.HasResidualGerbe.iff_existsMonoSurjectiveFlatSpecFieldAt :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] {x : Points X},
    HasResidualGerbe X x ↔ existsMonoSurjectiveFlatSpecFieldAt X x)

/- Definition 100.11.8 (2): if the residual gerbe of `X` at `x` exists, then it
is the strictly full subcategory `Z_x ⊂ X` constructed in Lemma 100.11.7. -/
@[stacks 06MU] #check (AlgebraicGeometry.AlgebraicStack.residualGerbe :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X)
    [HasResidualGerbe X x], GroupoidsOver S)
#check (AlgebraicGeometry.AlgebraicStack.residualGerbeι :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X)
    [HasResidualGerbe X x], residualGerbe X x ⟶ X)
#check (AlgebraicGeometry.AlgebraicStack.residualGerbe_properties :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X)
    [HasResidualGerbe X x],
    AlgebraicStack (residualGerbe X x) ∧ IsReduced (residualGerbe X x) ∧
      IsLocallyNoetherian (residualGerbe X x) ∧
      Nonempty (Points (residualGerbe X x)) ∧
      Subsingleton (Points (residualGerbe X x)) ∧
      (residualGerbeObjectProperty X x).IsClosedUnderIsomorphisms ∧
      (toFunctor (residualGerbeι X x)).Full ∧
      (toFunctor (residualGerbeι X x)).Faithful ∧
      Groupoids.Hom.Mono (residualGerbeι X x) ∧
      Set.range (Points.map (residualGerbeι X x)) = {x})

end AlgebraicGeometry.AlgebraicStack
