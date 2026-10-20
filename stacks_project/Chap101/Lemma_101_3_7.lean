/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.LocallySeparated
import StacksCheckRecall

/-!
# Locally separated representable morphisms of algebraic stacks

A morphism of algebraic stacks representable by algebraic spaces is locally
separated in the scheme-slice sense of algebraic spaces if and only if its
relative 2-diagonal is an immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

/- Lemma 101.3.7: Let `f : X ⟶ Y` be a morphism of algebraic stacks
representable by algebraic spaces. Then the following are equivalent: `f` is
locally separated, and `Hom.diagonal f` is an immersion. -/
@[stacks 04YU] #check (AlgebraicGeometry.Groupoids.Hom.locallySeparated_tfae :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y},
    relativelyRepresentableByAlgebraicSpaces f →
    List.TFAE
      [AlgebraicGeometry.Groupoids.Hom.has (@AlgebraicSpace.LocallySeparated S) f,
        AlgebraicGeometry.Groupoids.Hom.has (@AlgebraicSpace.IsImmersion S)
          (Hom.diagonal.{u + 1, u, u + 1} f)])
