/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap100.Lemma_100_11_2_LocallyOfFiniteType
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Diagonal.FiniteType

/-!
# Diagonals of morphisms of algebraic stacks

The relative 2-diagonal of a morphism of algebraic stacks is representable by
algebraic spaces and locally of finite type in the scheme-slice sense.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

#check
  (AlgebraicGeometry.Groupoids.Hom.relativelyRepresentableByAlgebraicSpaces_diagonal :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
      relativelyRepresentableByAlgebraicSpaces
        (Hom.diagonal.{u + 1, u, u + 1} f))

#check
  (AlgebraicGeometry.Groupoids.Hom.LocallyOfFiniteType.diagonal :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
      AlgebraicGeometry.Groupoids.Hom.LocallyOfFiniteType
        (Hom.diagonal.{u + 1, u, u + 1} f))

#check
  (AlgebraicGeometry.Groupoids.Hom.has_locallyOfFiniteType_diagonal :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
      AlgebraicGeometry.Groupoids.Hom.has (@AlgebraicSpace.LocallyOfFiniteType S)
        (Hom.diagonal.{u + 1, u, u + 1} f))
