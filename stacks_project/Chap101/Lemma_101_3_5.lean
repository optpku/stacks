/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.Separated
import StacksCheckRecall

/-!
# Separated representable morphisms of algebraic stacks

A morphism of algebraic stacks representable by algebraic spaces is separated
in the scheme-slice sense of algebraic spaces if and only if its relative
2-diagonal is a closed immersion, equivalently proper, equivalently
universally closed.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

/- Lemma 101.3.5: A morphism of algebraic stacks representable by algebraic
spaces is separated if and only if its relative 2-diagonal is a closed
immersion, equivalently proper, equivalently universally closed. -/
@[stacks 04YS] #check (AlgebraicGeometry.Groupoids.Hom.separated_tfae :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y},
    relativelyRepresentableByAlgebraicSpaces f →
    List.TFAE
      [AlgebraicGeometry.Groupoids.Hom.has (@AlgebraicSpace.Separated S) f,
        AlgebraicGeometry.Groupoids.Hom.has (@AlgebraicSpace.IsClosedImmersion S)
          (Hom.diagonal.{u + 1, u, u + 1} f),
        AlgebraicGeometry.Groupoids.Hom.has (@AlgebraicSpace.Proper S)
          (Hom.diagonal.{u + 1, u, u + 1} f),
        AlgebraicGeometry.Groupoids.Hom.has (@AlgebraicSpace.UniversallyClosed S)
          (Hom.diagonal.{u + 1, u, u + 1} f)])
