/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Unramified.Diagonal
import StacksCheckRecall

/-!
# Diagonal criterion for unramified morphisms of algebraic stacks

A morphism of algebraic stacks is unramified if and only if it is locally of
finite type and its relative 2-diagonal is étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Unramified

/- Lemma 101.36.9: a morphism `f : X ⟶ Y` of algebraic stacks is unramified
if and only if it is locally of finite type and its relative 2-diagonal
`Hom.diagonal f : X ⟶ X ×_Y X` is étale. -/
@[stacks 0CJ0] #check
  (AlgebraicGeometry.AlgebraicStack.Unramified.iff_locallyOfFiniteType_and_etale_diagonal :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    Unramified f ↔
      LocallyOfFiniteType f ∧ Etale (Hom.diagonal.{u + 1, u, u + 1} f))

/- An unramified morphism of algebraic stacks is locally of finite type. -/
#check (AlgebraicGeometry.AlgebraicStack.Unramified.locallyOfFiniteType :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Unramified f],
    LocallyOfFiniteType f)

/- The relative 2-diagonal of an unramified morphism of algebraic stacks is
étale. -/
#check (AlgebraicGeometry.AlgebraicStack.Unramified.etale_diagonal :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Unramified f],
    Etale (Hom.diagonal.{u + 1, u, u + 1} f))

/- A locally of finite type morphism of algebraic stacks whose relative
2-diagonal is étale is unramified. -/
#check (AlgebraicGeometry.AlgebraicStack.Unramified.of_etale_diagonal :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Etale (Hom.diagonal.{u + 1, u, u + 1} f)],
    Unramified f)

end AlgebraicGeometry.AlgebraicStack.Unramified
